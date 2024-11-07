#include "util/message.h"
#include <fstream>
#include <goto-symex/goto_trace.h>
#include <ostream>
#include <sstream>
#include <unordered_map>
#include <list>
#include <util/language.h>
#include <langapi/language_util.h>
#include <optional>
#include <filesystem>
#include <util/cmdline.h>
#include <nlohmann/json.hpp>
#include <regex>
#include <array>
#include <string>
#include <set>
#include <vector>
#include <numeric>
#include <iostream>
#include <util/type_byte_size.h>
#include <util/expr_util.h>
#include <irep2/irep2_expr.h>
#include <util/std_expr.h>
#include <util/mp_arith.h>
#include <memory>
#include <irep2/irep2_type.h>
#include <libdwarf/libdwarf.h>
#include <libdwarf/dwarf.h>
#include <fcntl.h>       // For O_RDONLY
#include <sys/mman.h>    // For mmap, PROT_READ, MAP_PRIVATE, etc.
#include <unistd.h>      // For close
#include <sys/types.h>   // For off_t
#include <cstring>       // For memcpy

// #include <boost/pfr.hpp>
// #include <boost/pfr/precise/core.hpp>

// template<typename T>
// void print_struct_fields(const T& obj, const std::string& prefix = "") {
//     try {
//         boost::pfr::for_each_field(obj, [&prefix](const auto& field, std::size_t idx) {
//             std::cout << prefix << "field " << idx << ": " << field << '\n';
//         });
//     } catch(const std::exception& e) {
//         std::cout << prefix << "Failed to print struct fields: " << e.what() << '\n';
//     }
// }

// Helper for ESBMC expr inspection using PFR when possible
// void inspect_expr_pfr(const expr2tc& expr, const namespacet& ns) {
//     std::cout << "\nPFR Struct Inspection:\n";
    
//     if(is_nil_expr(expr)) {
//         std::cout << "Nil expression\n";
//         return;
//     }

//     // Try to print the base expr2t
//     std::cout << "Base expression structure:\n";
//     print_struct_fields(*expr.get(), "  ");
    
//     if(is_pointer_type(expr->type)) {
//         try {
//             expr2tc deref = dereference2tc(expr->type, expr);
//             if(!is_nil_expr(deref)) {
//                 std::cout << "\nDereferenced structure:\n";
//                 print_struct_fields(*deref.get(), "  ");
                
//                 // If it's our DeviceRecord struct
//                 if(is_struct_type(deref->type)) {
//                     const struct_type2t& struct_type = to_struct_type(deref->type);
//                     std::cout << "\nStruct members:\n";
                    
//                     for(size_t i = 0; i < struct_type.members.size(); i++) {
//                         try {
//                             expr2tc member = member2tc(struct_type.members[i], deref, 
//                                                      struct_type.member_names[i]);
//                             std::cout << "  Member " << id2string(struct_type.member_names[i]) << ":\n";
//                             print_struct_fields(*member.get(), "    ");
//                         } catch(const std::exception& e) {
//                             std::cout << "  Failed to access member " 
//                                     << id2string(struct_type.member_names[i]) 
//                                     << ": " << e.what() << '\n';
//                         }
//                     }
//                 }
//             }
//         } catch(const std::exception& e) {
//             std::cout << "Dereference failed: " << e.what() << '\n';
//         }
//     }
    
//     // Try to print type information
//     if(!is_nil_type(expr->type)) {
//         std::cout << "\nType structure:\n";
//         print_struct_fields(*expr->type.get(), "  ");
        
//         if(is_pointer_type(expr->type)) {
//             const pointer_type2t& ptr_type = to_pointer_type(expr->type);
//             if(!is_nil_type(ptr_type.subtype)) {
//                 std::cout << "\nPointed-to type structure:\n";
//                 print_struct_fields(*ptr_type.subtype.get(), "  ");
//             }
//         }
//     }
// }

class DwarfInspector {
private:
    Dwarf_Debug dbg;
    Dwarf_Error error;
    int fd;

public:
    DwarfInspector(const char* filename) : dbg(nullptr), error(nullptr), fd(-1) {
        fd = open(filename, O_RDONLY);
        if (fd < 0) {
            throw std::runtime_error("Failed to open file");
        }

        if (dwarf_init(fd, DW_DLC_READ, nullptr, nullptr, &dbg, &error) != DW_DLV_OK) {
            close(fd);
            throw std::runtime_error("Failed to initialize DWARF");
        }
    }

    ~DwarfInspector() {
        if (dbg) {
            dwarf_finish(dbg, &error);
        }
        if (fd >= 0) {
            close(fd);
        }
    }

    void inspect_memory(void* ptr, size_t size) {
        Dwarf_Die cu_die = nullptr;
        Dwarf_Unsigned next_cu_header;

        // Iterate through compilation units
        while (dwarf_next_cu_header(dbg, nullptr, nullptr, nullptr, nullptr,
                                  &next_cu_header, &error) == DW_DLV_OK) {
            if (dwarf_siblingof(dbg, nullptr, &cu_die, &error) == DW_DLV_OK) {
                inspect_die_tree(cu_die, ptr, size);
                dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);
            }
        }
    }

private:
    void inspect_die_tree(Dwarf_Die die, void* ptr, size_t size) {
        Dwarf_Half tag;
        if (dwarf_tag(die, &tag, &error) != DW_DLV_OK) {
            return;
        }

        // Print DIE information
        print_die_info(die, tag, ptr, size);

        // Check for children
        Dwarf_Die child = nullptr;
        if (dwarf_child(die, &child, &error) == DW_DLV_OK) {
            inspect_die_tree(child, ptr, size);
            dwarf_dealloc(dbg, child, DW_DLA_DIE);
        }

        // Check for siblings
        Dwarf_Die sibling = nullptr;
        if (dwarf_siblingof(dbg, die, &sibling, &error) == DW_DLV_OK) {
            inspect_die_tree(sibling, ptr, size);
            dwarf_dealloc(dbg, sibling, DW_DLA_DIE);
        }
    }

    void print_die_info(Dwarf_Die die, Dwarf_Half tag, void* ptr, size_t size) {
        char* die_name = nullptr;
        if (dwarf_diename(die, &die_name, &error) == DW_DLV_OK) {
            std::cout << "DIE Name: " << die_name << "\n";
            dwarf_dealloc(dbg, die_name, DW_DLA_STRING);
        }

        // Handle different types of DIEs
        switch (tag) {
            case DW_TAG_base_type:
                print_base_type(die, ptr);
                break;
            case DW_TAG_structure_type:
                print_struct_type(die, ptr);
                break;
            case DW_TAG_pointer_type:
                print_pointer_type(die, ptr);
                break;
            case DW_TAG_array_type:
                print_array_type(die, ptr);
                break;
        }
    }

    void print_base_type(Dwarf_Die die, void* ptr) {
        Dwarf_Unsigned size;
        if (dwarf_bytesize(die, &size, &error) == DW_DLV_OK) {
            std::cout << "Base Type Size: " << size << " bytes\n";
            
            // Print value based on size
            switch(size) {
                case 1: // char
                    std::cout << "Value: " << *(char*)ptr << "\n";
                    break;
                case 4: // int
                    std::cout << "Value: " << *(int*)ptr << "\n";
                    break;
                case 8: // long
                    std::cout << "Value: " << *(long*)ptr << "\n";
                    break;
            }
        }
    }

    void print_struct_type(Dwarf_Die die, void* ptr) {
        Dwarf_Unsigned size;
        if (dwarf_bytesize(die, &size, &error) == DW_DLV_OK) {
            std::cout << "Struct Size: " << size << " bytes\n";
        }

        // Print member information
        Dwarf_Die child = nullptr;
        if (dwarf_child(die, &child, &error) == DW_DLV_OK) {
            do {
                Dwarf_Half child_tag;
                if (dwarf_tag(child, &child_tag, &error) == DW_DLV_OK) {
                    if (child_tag == DW_TAG_member) {
                        print_member_info(child, ptr);
                    }
                }
            } while (dwarf_siblingof(dbg, child, &child, &error) == DW_DLV_OK);
            dwarf_dealloc(dbg, child, DW_DLA_DIE);
        }
    }

    void print_member_info(Dwarf_Die member_die, void* struct_ptr) {
        char* member_name = nullptr;
        if (dwarf_diename(member_die, &member_name, &error) == DW_DLV_OK) {
            std::cout << "Member: " << member_name << "\n";
            
            // Get member location
            Dwarf_Attribute loc_attr;
            if (dwarf_attr(member_die, DW_AT_data_member_location, &loc_attr, &error) == DW_DLV_OK) {
                Dwarf_Unsigned offset;
                if (dwarf_formudata(loc_attr, &offset, &error) == DW_DLV_OK) {
                    void* member_ptr = (char*)struct_ptr + offset;
                    
                    // Get member type and print its value
                    Dwarf_Die type_die;
                    if (get_type_die(member_die, &type_die)) {
                        print_die_info(type_die, DW_TAG_base_type, member_ptr, 0);
                        dwarf_dealloc(dbg, type_die, DW_DLA_DIE);
                    }
                }
                dwarf_dealloc(dbg, loc_attr, DW_DLA_ATTR);
            }
            dwarf_dealloc(dbg, member_name, DW_DLA_STRING);
        }
    }

    void print_pointer_type(Dwarf_Die die, void* ptr) {
        void* pointed_value = *(void**)ptr;
        std::cout << "Pointer Value: " << pointed_value << "\n";

        if (pointed_value != nullptr) {
            // Get type of pointed-to data
            Dwarf_Die type_die;
            if (get_type_die(die, &type_die)) {
                print_die_info(type_die, DW_TAG_base_type, pointed_value, 0);
                dwarf_dealloc(dbg, type_die, DW_DLA_DIE);
            }
        }
    }

    void print_array_type(Dwarf_Die die, void* ptr) {
        Dwarf_Die type_die;
        if (get_type_die(die, &type_die)) {
            Dwarf_Unsigned elem_size;
            if (dwarf_bytesize(type_die, &elem_size, &error) == DW_DLV_OK) {
                // Try to get array size
                Dwarf_Attribute size_attr;
                if (dwarf_attr(die, DW_AT_count, &size_attr, &error) == DW_DLV_OK) {
                    Dwarf_Unsigned count;
                    if (dwarf_formudata(size_attr, &count, &error) == DW_DLV_OK) {
                        std::cout << "Array Size: " << count << " elements\n";
                        
                        // Print each element
                        for (Dwarf_Unsigned i = 0; i < count; i++) {
                            void* elem_ptr = (char*)ptr + (i * elem_size);
                            std::cout << "Element " << i << ": ";
                            print_die_info(type_die, DW_TAG_base_type, elem_ptr, 0);
                        }
                    }
                    dwarf_dealloc(dbg, size_attr, DW_DLA_ATTR);
                }
            }
            dwarf_dealloc(dbg, type_die, DW_DLA_DIE);
        }
    }

    bool get_type_die(Dwarf_Die die, Dwarf_Die* type_die) {
        Dwarf_Attribute type_attr;
        if (dwarf_attr(die, DW_AT_type, &type_attr, &error) == DW_DLV_OK) {
            Dwarf_Off type_offset;
            if (dwarf_global_formref(type_attr, &type_offset, &error) == DW_DLV_OK) {
                if (dwarf_offdie(dbg, type_offset, type_die, &error) == DW_DLV_OK) {
                    dwarf_dealloc(dbg, type_attr, DW_DLA_ATTR);
                    return true;
                }
            }
            dwarf_dealloc(dbg, type_attr, DW_DLA_ATTR);
        }
        return false;
    }
};


using json = nlohmann::json;

static json tests_json;
static bool first_write = true;
static std::map<std::string, std::vector<std::string>> source_files;

std::vector<std::string> include_paths = {
    "/usr/include",
    "/usr/local/include"
    // Add other system include paths
};


/// Namespace for scripts taken from Clang, as generated by:
/// clang --analyze -Xclang -analyzer-output=html -o test test.c
namespace clang_bug_report
{
// Keep all existing clang_bug_report style definitions here
constexpr std::string_view html_style{
  R"(<style type="text/css">
body { color:#000000; background-color:#ffffff }
body { font-family:Helvetica, sans-serif; font-size:10pt }
h1 { font-size:14pt }
.FileName { margin-top: 5px; margin-bottom: 5px; display: inline; }
.FileNav { margin-left: 5px; margin-right: 5px; display: inline; }
.FileNav a { text-decoration:none; font-size: larger; }
.divider { margin-top: 30px; margin-bottom: 30px; height: 15px; }
.divider { background-color: gray; }
.code { border-collapse:collapse; width:100%; }
.code { font-family: "Monospace", monospace; font-size:10pt }
.code { line-height: 1.2em }
.comment { color: green; font-style: oblique }
.keyword { color: blue }
.string_literal { color: red }
.directive { color: darkmagenta }

/* Macros and variables could have pop-up notes hidden by default.
  - Macro pop-up:    expansion of the macro
  - Variable pop-up: value (table) of the variable */
.macro_popup, .variable_popup { display: none; }

/* Pop-up appears on mouse-hover event. */
.macro:hover .macro_popup, .variable:hover .variable_popup {
  display: block;
  padding: 2px;
  -webkit-border-radius:5px;
  -webkit-box-shadow:1px 1px 7px #000;
  border-radius:5px;
  box-shadow:1px 1px 7px #000;
  position: absolute;
  top: -1em;
  left:10em;
  z-index: 1
}

.macro_popup {
  border: 2px solid red;
  background-color:#FFF0F0;
  font-weight: normal;
}

.variable_popup {
  border: 2px solid blue;
  background-color:#F0F0FF;
  font-weight: bold;
  font-family: Helvetica, sans-serif;
  font-size: 9pt;
}

/* Pop-up notes needs a relative position as a base where they pops up. */
.macro, .variable {
  background-color: PaleGoldenRod;
  position: relative;
}
.macro { color: DarkMagenta; }

#tooltiphint {
  position: fixed;
  width: 50em;
  margin-left: -25em;
  left: 50%;
  padding: 10px;
  border: 1px solid #b0b0b0;
  border-radius: 2px;
  box-shadow: 1px 1px 7px black;
  background-color: #c0c0c0;
  z-index: 2;
}

.num { width:2.5em; padding-right:2ex; background-color:#eeeeee }
.num { text-align:right; font-size:8pt }
.num { color:#444444 }
.line { padding-left: 1ex; border-left: 3px solid #ccc }
.line { white-space: pre }
.msg { -webkit-box-shadow:1px 1px 7px #000 }
.msg { box-shadow:1px 1px 7px #000 }
.msg { -webkit-border-radius:5px }
.msg { border-radius:5px }
.msg { font-family:Helvetica, sans-serif; font-size:8pt }
.msg { float:left }
.msg { position:relative }
.msg { padding:0.25em 1ex 0.25em 1ex }
.msg { margin-top:10px; margin-bottom:10px }
.msg { font-weight:bold }
.msg { max-width:60em; word-wrap: break-word; white-space: pre-wrap }
.msgT { padding:0x; spacing:0x }
.msgEvent { background-color:#fff8b4; color:#000000 }
.msgControl { background-color:#bbbbbb; color:#000000 }
.msgNote { background-color:#ddeeff; color:#000000 }
.mrange { background-color:#dfddf3 }
.mrange { border-bottom:1px solid #6F9DBE }
.PathIndex { font-weight: bold; padding:0px 5px; margin-right:5px; }
.PathIndex { -webkit-border-radius:8px }
.PathIndex { border-radius:8px }
.PathIndexEvent { background-color:#bfba87 }
.PathIndexControl { background-color:#8c8c8c }
.PathIndexPopUp { background-color: #879abc; }
.PathNav a { text-decoration:none; font-size: larger }
.CodeInsertionHint { font-weight: bold; background-color: #10dd10 }
.CodeRemovalHint { background-color:#de1010 }
.CodeRemovalHint { border-bottom:1px solid #6F9DBE }
.msg.selected{ background-color:orange !important; }

table.simpletable {
  padding: 5px;
  font-size:12pt;
  margin:20px;
  border-collapse: collapse; border-spacing: 0px;
}
td.rowname {
  text-align: right;
  vertical-align: top;
  font-weight: bold;
  color:#444444;
  padding-right:2ex;
}

/* Hidden text. */
input.spoilerhider + label {
  cursor: pointer;
  text-decoration: underline;
  display: block;
}
input.spoilerhider {
 display: none;
}
input.spoilerhider ~ .spoiler {
  overflow: hidden;
  margin: 10px auto 0;
  height: 0;
  opacity: 0;
}
input.spoilerhider:checked + label + .spoiler{
  height: auto;
  opacity: 1;
}
</style>)"};
constexpr std::string_view annotated_source_header_fmt{
  R"(
<h3>Annotated Source Code</h3>
<p>Press <a href="#" onclick="toggleHelp(); return false;">'?'</a>
   to see keyboard shortcuts</p>
<input type="checkbox" class="spoilerhider" id="showinvocation" />
<label for="showinvocation" >Show analyzer invocation</label>
<div class="spoiler">{}
</div>
<div id='tooltiphint' hidden="true">
  <p>Keyboard shortcuts: </p>
  <ul>
    <li>Use 'j/k' keys for keyboard navigation</li>
    <li>Use 'Shift+S' to show/hide relevant lines</li>
    <li>Use '?' to toggle this window</li>
  </ul>
  <a href="#" onclick="toggleHelp(); return false;">Close</a>
</div>
)"};

// NOTE: Removed the "Show arrows"
constexpr std::string_view counterexample_checkbox{R"(<form>
    <input type="checkbox" name="showCounterexample" id="showCounterexample" />
    <label for="showCounterexample">
       Show only relevant lines
    </label>
</form>)"};

const std::string
counterexample_filter(const std::string_view relevant_lines_js)
{
  std::ostringstream oss;
  oss << "<script type='text/javascript'>\n";
  oss << "var relevant_lines = " << relevant_lines_js << ";\n";
  oss << R"(
var filterCounterexample = function (hide) {
  var tables = document.getElementsByClassName("code");
  for (var t=0; t<tables.length; t++) {
    var table = tables[t];
    var file_id = table.getAttribute("data-fileid");
    var lines_in_fid = relevant_lines[file_id];
    if (!lines_in_fid) {
      lines_in_fid = {};
    }
    var lines = table.getElementsByClassName("codeline");
    for (var i=0; i<lines.length; i++) {
        var el = lines[i];
        var lineNo = el.getAttribute("data-linenumber");
        if (!lines_in_fid[lineNo]) {
          if (hide) {
            el.setAttribute("hidden", "");
          } else {
            el.removeAttribute("hidden");
          }
        }
    }
  }
}


window.addEventListener("keydown", function (event) {
  if (event.defaultPrevented) {
    return;
  }
  // SHIFT + S
  if (event.shiftKey && event.keyCode == 83) {
    var checked = document.getElementsByName("showCounterexample")[0].checked;
    filterCounterexample(!checked);
    document.getElementsByName("showCounterexample")[0].click();
  } else {
    return;
  }
  event.preventDefault();
}, true);

document.addEventListener("DOMContentLoaded", function() {
    document.querySelector('input[name="showCounterexample"]').onchange=
        function (event) {
      filterCounterexample(this.checked);
    };
});
</script>)";

  return oss.str();
}
constexpr std::string_view keyboard_navigation_js{R"(  
<script type='text/javascript'>
var digitMatcher = new RegExp("[0-9]+");

var querySelectorAllArray = function(selector) {
  return Array.prototype.slice.call(
    document.querySelectorAll(selector));
}

document.addEventListener("DOMContentLoaded", function() {
    querySelectorAllArray(".PathNav > a").forEach(
        function(currentValue, currentIndex) {
            var hrefValue = currentValue.getAttribute("href");
            currentValue.onclick = function() {
                scrollTo(document.querySelector(hrefValue));
                return false;
            };
        });
});

var findNum = function() {
    var s = document.querySelector(".msg.selected");
    if (!s || s.id == "EndPath") {
        return 0;
    }
    var out = parseInt(digitMatcher.exec(s.id)[0]);
    return out;
};

var classListAdd = function(el, theClass) {
  if(!el.className.baseVal)
    el.className += " " + theClass;
  else
    el.className.baseVal += " " + theClass;
};

var classListRemove = function(el, theClass) {
  var className = (!el.className.baseVal) ?
      el.className : el.className.baseVal;
    className = className.replace(" " + theClass, "");
  if(!el.className.baseVal)
    el.className = className;
  else
    el.className.baseVal = className;
};

var scrollTo = function(el) {
    querySelectorAllArray(".selected").forEach(function(s) {
      classListRemove(s, "selected");
    });
    classListAdd(el, "selected");
    window.scrollBy(0, el.getBoundingClientRect().top -
        (window.innerHeight / 2));
    highlightArrowsForSelectedEvent();
};

var move = function(num, up, numItems) {
  if (num == 1 && up || num == numItems - 1 && !up) {
    return 0;
  } else if (num == 0 && up) {
    return numItems - 1;
  } else if (num == 0 && !up) {
    return 1 % numItems;
  }
  return up ? num - 1 : num + 1;
}

var numToId = function(num) {
  if (num == 0) {
    return document.getElementById("EndPath")
  }
  return document.getElementById("Path" + num);
};

var navigateTo = function(up) {
  var numItems = document.querySelectorAll(
      ".line > .msgEvent, .line > .msgControl").length;
  var currentSelected = findNum();
  var newSelected = move(currentSelected, up, numItems);
  var newEl = numToId(newSelected, numItems);

  // Scroll element into center.
  scrollTo(newEl);
};

window.addEventListener("keydown", function (event) {
  if (event.defaultPrevented) {
    return;
  }
  // key 'j'
  if (event.keyCode == 74) {
    navigateTo(/*up=*/false);
  // key 'k'
  } else if (event.keyCode == 75) {
    navigateTo(/*up=*/true);
  } else {
    return;
  }
  event.preventDefault();
}, true);
</script>
  
<script type='text/javascript'>

var toggleHelp = function() {
    var hint = document.querySelector("#tooltiphint");
    var attributeName = "hidden";
    if (hint.hasAttribute(attributeName)) {
      hint.removeAttribute(attributeName);
    } else {
      hint.setAttribute("hidden", "true");
    }
};
window.addEventListener("keydown", function (event) {
  if (event.defaultPrevented) {
    return;
  }
  if (event.key == "?") {
    toggleHelp();
  } else {
    return;
  }
  event.preventDefault();
});
</script>)"};

} // namespace clang_bug_report

class html_report
{
public:
  html_report(
    const goto_tracet &goto_trace,
    const namespacet &ns,
    const cmdlinet::options_mapt &options_map);
  void output(std::ostream &oss) const;
  static const std::vector<std::string>& get_file_lines(const std::string& filename);

  bool show_partial_assertions = false;

protected:
  const std::string generate_head() const;
  const std::string generate_body() const;
  const goto_tracet &goto_trace;

private:
  static constexpr std::array<const char*, 32> keywords{{
    "auto",     "break",  "case",    "char",   "const",    "continue",
    "default",  "do",     "double",  "else",   "enum",     "extern",
    "float",    "for",    "goto",    "if",     "int",      "long",
    "register", "return", "short",   "signed", "sizeof",   "static",
    "struct",   "switch", "typedef", "union",  "unsigned", "void",
    "volatile", "while"
  }};
  
  // Cache for file contents
  static std::unordered_map<std::string, std::vector<std::string>> file_cache;
  
  // Pre-compiled regex patterns 
  static std::vector<std::regex> keyword_patterns;
  static void init_patterns();
  static bool patterns_initialized;

  const namespacet &ns;
  const cmdlinet::options_mapt &opt_map;
  std::optional<goto_trace_stept> violation_step;
  void print_file_table(
    std::ostream &os,
    std::pair<const std::string_view, size_t>) const;

  struct code_lines
  {
    explicit code_lines(const std::string &content) : content(content)
    {
    }
    const std::string content;
    std::string to_html() const;
  };
  struct code_steps
  {
    code_steps(const size_t step, const std::string &msg, bool is_jump)
      : step(step), msg(msg), is_jump(is_jump)
    {
    }
    size_t step;
    std::string msg;
    bool is_jump;
    size_t file_id = 1;
    std::string to_html(size_t last) const;
  };

  static inline const std::string
  tag_body_str(const std::string_view tag, const std::string_view body)
  {
    return fmt::format("<{0}>{1}</{0}>", tag, body);
  }
};

// Static member definitions
std::unordered_map<std::string, std::vector<std::string>> html_report::file_cache;
std::vector<std::regex> html_report::keyword_patterns;
bool html_report::patterns_initialized = false;

void html_report::init_patterns() 
{
  if(!patterns_initialized) {
    keyword_patterns.reserve(keywords.size());
    for(const auto& word : keywords) {
      keyword_patterns.push_back(
        std::regex(fmt::format("(\\b({}))(\\b)(?=[^\"]*(\"[^\"]*\"[^\"]*)*$)", word)));
    }
    patterns_initialized = true;
  }
}

const std::vector<std::string>& html_report::get_file_lines(const std::string& filename)
{
  auto it = file_cache.find(filename);
  if(it != file_cache.end()) {
    return it->second;
  }

  std::vector<std::string> lines;
  lines.reserve(500);
  
  std::ifstream input(filename);
  std::string line;
  while(std::getline(input, line)) {
    lines.push_back(std::move(line));
  }

  return file_cache.emplace(filename, std::move(lines)).first->second;
}

html_report::html_report(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const cmdlinet::options_mapt &options_map)
  : goto_trace(goto_trace), ns(ns), opt_map(options_map)
{
  init_patterns();  // Initialize regex patterns once
  
  for (const goto_trace_stept &step : goto_trace.steps) {
    if (step.is_assert() && !step.guard) {
      violation_step = step;
      return;
    }
  }
  log_error("[HTML] Could not find any asserts in error trace!");
  abort();
}

const std::string html_report::generate_head() const
{
  std::ostringstream head;
  {
    head << tag_body_str("title", "ESBMC report");
    head << clang_bug_report::html_style;
  }
  return tag_body_str("head", head.str());
}
const std::string html_report::generate_body() const
{
  std::ostringstream body;
  const locationt &location = violation_step->pc->location;
  const std::string filename{
    std::filesystem::absolute(location.get_file().as_string()).string()};
  // Bug Summary
  {
    const std::string position{fmt::format(
      "function {}, line {}, column {}",
      location.get_function(),
      location.get_line(),
      location.get_column())};
    std::string violation_str{violation_step->comment};
    if (violation_str.empty())
      violation_str = "Assertion failure";
    violation_str[0] = toupper(violation_str[0]);
    body << "<h3>Bug Summary</h3>";
    body << R"(<table class="simpletable">)";
    body << fmt::format(
      R"(<tr><td class="rowname">File:</td><td>{}</td></tr>)", filename);
    body << fmt::format(
      R"(<tr><td class="rowname">Violation:</td><td><a href="#EndPath">{}</a><br />{}</td></tr></table>)",
      position,
      violation_str);
  }

  // Annoted Source Header
  {
    std::ostringstream oss;
    for (const auto &item : opt_map)
    {
      oss << item.first << " ";
      for (const std::string &value : item.second)
        oss << value << " ";
    }
    body << fmt::format(
      clang_bug_report::annotated_source_header_fmt, oss.str());
  }

  std::set<std::string> files;
  // Counter-Example filtering
  {
    std::unordered_set<size_t> relevant_lines;
    for (const auto &step : goto_trace.steps)
    {
      files.insert(step.pc->location.get_file().as_string());
      if (!(step.is_assert() && step.guard))
        relevant_lines.insert(atoi(step.pc->location.get_line().c_str()));
    }

    // TODO: Every file!
    std::ostringstream oss;
    oss << R"({"1": {)";
    for (const auto line : relevant_lines)
      oss << fmt::format("\"{}\": 1,", line);
    oss << "}}";
    body << clang_bug_report::counterexample_filter(oss.str());
    body << clang_bug_report::counterexample_checkbox;
    body << clang_bug_report::keyboard_navigation_js;
  }
  // Counter-Example and Arrows
  {
    for (const std::string &file : files)
    {
      print_file_table(
        body, {file, 1 + std::distance(files.begin(), files.find(file))});
    }
  }

  return tag_body_str("body", body.str());
}

void html_report::print_file_table(
  std::ostream &os,
  std::pair<const std::string_view, size_t> file) const
{
  const auto& lines = get_file_lines(std::string(file.first));

  os << fmt::format(
    "<div id=File{}><h4 class=FileName>{}</h4>",
    file.second,
    std::filesystem::absolute(file.first).string());

  std::unordered_map<size_t, std::vector<code_steps>> steps;
  size_t counter = 0;
  steps.reserve(goto_trace.steps.size() / 2);

  for (const auto &step : goto_trace.steps)
  {
    if (step.pc->location.get_file().as_string() != file.first)
    {
      counter++;
      continue;
    }
    
    size_t line = atoi(step.pc->location.get_line().c_str());
    std::string msg;
    
    if (step.pc->is_assume())
      msg = "Assumption restriction";
    else if (step.pc->is_assert() || step.is_assert())
    {
      if (!show_partial_assertions && step.guard)
        continue;

      msg = (step.comment.empty() ? "Assertion check" : step.comment);
      msg[0] = toupper(msg[0]);
    }
    else if (step.pc->is_assign())
    {
      msg = from_expr(ns, "", step.lhs);
      if (is_nil_expr(step.value))
        msg += " (assignment removed)";
      else
        msg += " = " + from_expr(ns, "", step.value);
    }
    else if (step.pc->is_function_call())
    {
      msg = "Function argument '";
      msg += from_expr(ns, "", step.lhs);
      msg += " = " + from_expr(ns, "", step.value) + "'";
    }

    steps[line].emplace_back(++counter, std::move(msg), 
                           step.is_assume() || step.is_assert());

    // Is this step the violation?
    if (step.is_assert() && !step.guard)
      break;
  }
  // Table begin
  os << fmt::format(R"(<table class="code" data-fileid="{}">)", file.second);
  for (size_t i = 0; i < lines.size(); i++)
  {
    const auto &it = steps.find(i);
    if (it != steps.end())
    {
      for (const auto &step : it->second)
      {
        os << step.to_html(counter);
      }
    }
    constexpr std::string_view codeline_fmt{
      R"(<tr class="codeline" data-linenumber="{0}"><td class="num" id="LN{0}">{0}</td><td class="line">{1}</td></tr>)"};
    
    code_lines code_line(lines[i]);
    os << fmt::format(codeline_fmt, i + 1, code_line.to_html());
  }

  os << "</table><hr class=divider>";
  // Table end
}

void html_report::output(std::ostream &oss) const
{
  std::ostringstream html;
  html << generate_head();
  html << generate_body();

  oss << "<!doctype html>";
  oss << tag_body_str("html", html.str());
}

std::string html_report::code_lines::to_html() const
{
  std::string output(content);
  for (size_t i = 0; i < html_report::keyword_patterns.size(); i++) {
    output = std::regex_replace(
      output, html_report::keyword_patterns[i],
      fmt::format("<span class='keyword'>{}</span>", 
                 html_report::keywords[i]));
  }
  return output;
}

std::string html_report::code_steps::to_html(size_t last) const
{
  constexpr double margin = 1;

  const std::string next_step =
    step + 1 == last ? "EndPath" : fmt::format("Path{}", step + 1);
  const std::string previous_step =
    step != 0 ? fmt::format("Path{}", step - 1) : "";

  constexpr std::string_view next_step_format{
    R"(<td><div class="PathNav"><a href="#{}" title="Next event ({}) ">&#x2192;</a></div></td>)"};
  const std::string next_step_str =
    step < last ? fmt::format(next_step_format, next_step, step + 1) : "";

  constexpr std::string_view previous_step_format{
    R"(<td><div class="PathNav"><a href="#{}" title="Previous event ({}) ">&#x2190;</a></div></td>)"};

  const std::string previous_step_str =
    step != 0 ? fmt::format(previous_step_format, previous_step, step - 1) : "";

  constexpr std::string_view jump_format{
    R"(<tr><td class="num"></td><td class="line"><div id="Path{0}" class="msg msgControl" style="margin-left:{1}ex"><table class="msgT"><tr><td valign="top"><div class="PathIndex PathIndexControl">{0}</div></td>{2}<td>{3}</td>{4}</tr></table></div></td></tr>)"};

  constexpr std::string_view step_format{
    R"(<tr><td class="num"></td><td class="line"><div id="Path{0}" class="msg msgEvent" style="margin-left:{1}ex"><table class="msgT"><tr><td valign="top"><div class="PathIndex PathIndexEvent">{0}</div></td>{2}<td>{3}</td>{4}</tr></table></div></td></tr>)"};

  constexpr std::string_view end_format{
    R"(<tr><td class="num"></td><td class="line"><div id="EndPath" class="msg msgEvent" style="margin-left:{1}ex"><table class="msgT"><tr><td valign="top"><div class="PathIndex PathIndexEvent">{0}</div></td>{2}<td>{3}</td></table></div></td></tr>)"};

  std::string format(is_jump ? jump_format : step_format);
  return fmt::format(
    step == last ? end_format : format,
    step,
    margin * step + 1,
    previous_step_str,
    msg,
    next_step_str);
}

std::string resolve_header_path(const std::string& header, const std::string& base_path) {
    // Try relative to the current file
    std::filesystem::path local_path = std::filesystem::path(base_path) / header;
    if (std::filesystem::exists(local_path)) {
        std::string resolved = std::filesystem::canonical(local_path).string();
        // Only skip if it's in /usr
        if (resolved.find("/usr/") != 0) {
            return resolved;
        }
    }
    
    // If header is absolute path and not in /usr, return it
    if (header[0] == '/' && header.find("/usr/") != 0) {
        if (std::filesystem::exists(header)) {
            return std::filesystem::canonical(header).string();
        }
    }
    
    return ""; // Return empty if not found or is in /usr
}

std::set<std::string> find_included_headers(const std::string& file_path, std::set<std::string>& processed_files) {
    if (processed_files.find(file_path) != processed_files.end() || 
        file_path.find("/usr/") == 0) { // Only skip /usr paths
        return {};
    }
    processed_files.insert(file_path);
    
    std::set<std::string> headers;
    std::ifstream source_file(file_path);
    std::string line;
    
    if (!source_file.is_open()) {
        return headers;
    }

    std::regex include_pattern(R"(#\s*include\s*([<"])([\w./]+)[>"])");
    
    while (std::getline(source_file, line)) {
        std::smatch match;
        if (std::regex_search(line, match, include_pattern)) {
            std::string header = match[2].str();
            
            // Resolve header path
            std::string resolved_path = resolve_header_path(header, 
                std::filesystem::path(file_path).parent_path().string());
            
            // Only process if it's a valid path and not in /usr
            if (!resolved_path.empty()) {
                headers.insert(resolved_path);
                
                // Recursively process this header
                auto nested_headers = find_included_headers(resolved_path, processed_files);
                headers.insert(nested_headers.begin(), nested_headers.end());
            }
        }
    }
    
    return headers;
}

void dump_expr_recursive(const expr2tc& expr, int depth = 0) {
    std::string indent(depth * 2, ' ');
    auto print_fn = [depth](const char* fmt, ...) {
        std::string indent(depth * 2, ' ');
        va_list args;
        va_start(args, fmt);
        std::cout << indent;
        vprintf(fmt, args);
        va_end(args);
    };

    if(is_nil_expr(expr)) {
        std::cout << indent << "<nil>\n";
        return;
    }

    // Dump the main expr2t structure
    std::cout << indent << "expr2tc at " << expr.get() << " {\n";
    __builtin_dump_struct(expr.get(), print_fn);

    // If it has a type, recursively dump that
    if(!is_nil_type(expr->type)) {
        std::cout << indent << "  type details {\n";
        __builtin_dump_struct(expr->type.get(), print_fn);
        
        // For pointer types, follow the subtype
        if(is_pointer_type(expr->type)) {
            const pointer_type2t& ptr_type = to_pointer_type(expr->type);
            std::cout << indent << "    pointed to type {\n";
            __builtin_dump_struct(ptr_type.subtype.get(), print_fn);
            std::cout << indent << "    }\n";
        }
        // For struct types, dump all member types
        else if(is_struct_type(expr->type)) {
            const struct_type2t& struct_type = to_struct_type(expr->type);
            std::cout << indent << "    member types {\n";
            for(size_t i = 0; i < struct_type.members.size(); i++) {
                std::cout << indent << "      member " << i << " (" 
                         << id2string(struct_type.member_names[i]) << ") {\n";
                __builtin_dump_struct(struct_type.members[i].get(), print_fn);
                std::cout << indent << "      }\n";
            }
            std::cout << indent << "    }\n";
        }
        std::cout << indent << "  }\n";
    }

    // If it's a symbol, dump the symbol details
    if(is_symbol2t(expr)) {
        const symbol2t& sym = to_symbol2t(expr);
        std::cout << indent << "  symbol details {\n";
        std::cout << indent << "    name: " << sym.thename << "\n";
        std::cout << indent << "  }\n";
    }
    
    // If it's a constant, dump the constant value
    if(is_constant_int2t(expr)) {
        const constant_int2t& c = to_constant_int2t(expr);
        std::cout << indent << "  constant value: " << c.value << "\n";
    }
    else if(is_constant_string2t(expr)) {
        const constant_string2t& c = to_constant_string2t(expr);
        std::cout << indent << "  constant value: \"" << c.value << "\"\n";
    }

    std::cout << indent << "}\n";
}

void print_expr_info(const std::string& context, const expr2tc& expr, const namespacet& ns) {
    std::cout << "\nDEBUG " << context << ":\n";
    
    if(is_nil_expr(expr)) {
        std::cout << "  <nil>\n";
        return;
    }

    // Basic info
    std::cout << "  Expression ID: " << get_expr_id(expr) << "\n";
    std::cout << "  Raw pointer: " << expr.get() << "\n";
    std::cout << "  Value: " << from_expr(ns, "", expr) << "\n";

    // Dump complete recursive structure
    std::cout << "  Complete structure dump:\n";
    dump_expr_recursive(expr);

    // Try to dereference if it's a pointer
    if(is_pointer_type(expr->type)) {
        try {
            expr2tc deref = dereference2tc(expr->type, expr);
            if(!is_nil_expr(deref)) {
                std::cout << "  Dereferenced value details:\n";
                dump_expr_recursive(deref, 2);
            }
        } catch(const std::exception& e) {
            std::cout << "  Failed to dereference: " << e.what() << "\n";
        } catch(...) {
            std::cout << "  Failed to dereference (unknown error)\n";
        }
    }
}

// Function to use with ESBMC
void inspect_device_memory(const expr2tc& expr, const namespacet& ns) {
    if(is_pointer_type(expr->type)) {
        try {
            if(is_symbol2t(expr)) {
                const symbol2t& sym = to_symbol2t(expr);
                
                // Get the binary path - this needs to be implemented
                const char* binary_path = get_binary_path();  // You need to implement this
                
                DwarfInspector inspector(binary_path);
                
                // Get the actual memory address - this needs to be implemented
                void* ptr = nullptr;  // You need to implement getting the actual pointer
                size_t size = sizeof(void*);
                
                inspector.inspect_memory(ptr, size);
            }
        } catch(const std::exception& e) {
            std::cout << "Memory inspection failed: " << e.what() << "\n";
        }
    }
}

std::string get_struct_values(const namespacet& ns, const expr2tc& expr, int depth = 0) {
    std::cout << "\nDEBUG Detailed type analysis ---------------\n";
    
    if(is_nil_expr(expr)) {
        return "null";
    }

    if(is_pointer_type(expr->type)) {
        std::cout << "DEBUG: Pointer analysis:\n";
        std::string raw_val = from_expr(ns, "", expr);
        std::cout << "Raw pointer value: " << raw_val << "\n";
        
        // First use clang dump to understand the memory layout
        try {
            auto print_fn = [](const char* fmt, ...) {
                va_list args;
                va_start(args, fmt);
                std::cout << "DEBUG struct dump: ";
                vprintf(fmt, args);
                va_end(args);
            };

            std::cout << "DEBUG: Pointer type details:\n";
            const expr2t* expr_ptr = expr.get();
            if(expr_ptr) {
                std::cout << "DEBUG: About to dump expr at " << expr_ptr << "\n";
                __builtin_dump_struct(expr_ptr, print_fn);
            }

            // Now attempt to get the underlying structure
            const pointer_type2t &ptr_type = to_pointer_type(expr->type);
            if(is_struct_type(ptr_type.subtype)) {
                const struct_type2t &struct_type = to_struct_type(ptr_type.subtype);
                json struct_data;
                
                // Log the struct layout we found
                std::cout << "DEBUG: Struct analysis after dump:\n";
                std::cout << "  Members found: " << struct_type.members.size() << "\n";
                
                for(size_t i = 0; i < struct_type.members.size(); i++) {
                    const irep_idt& member_name = struct_type.member_names[i];
                    const type2tc& member_type = struct_type.members[i];
                    
                    std::cout << "  Member " << i << ":\n";
                    std::cout << "    Name: " << member_name << "\n";
                    std::cout << "    Type ID: " << get_type_id(member_type) << "\n";
                    
                    try {
                        // Try to create a member access expression
                        expr2tc member_expr = member2tc(member_type, expr, member_name);
                        
                        // Log the expression we created
                        std::cout << "    Created member expression\n";
                        print_expr_info("member_expr", member_expr, ns);
                        
                        // Recursively analyze this member
                        struct_data[id2string(member_name)] = get_struct_values(ns, member_expr, depth + 1);
                    } catch(const std::exception& e) {
                        std::cout << "    Error accessing member: " << e.what() << "\n";
                        struct_data[id2string(member_name)] = "access-error";
                    }
                }
                
                return struct_data.dump();
            }
        } catch(const std::exception& e) {
            std::cout << "DEBUG: Exception during struct analysis: " << e.what() << "\n";
        }

        // Fallback to basic pointer value if we couldn't analyze structure
        if(raw_val == "0" || raw_val == "NULL" || raw_val.empty()) {
            return "null";
        }
        if(raw_val.find("invalid-object") != std::string::npos) {
            return "\"invalid-object\"";
        }
        return "\"" + raw_val + "\"";
    }
    
    if(is_struct_type(expr->type)) {
        try {
            auto print_fn = [](const char* fmt, ...) {
                va_list args;
                va_start(args, fmt);
                std::cout << "DEBUG struct dump: ";
                vprintf(fmt, args);
                va_end(args);
            };

            // Dump the struct layout first
            const expr2t* expr_ptr = expr.get();
            if(expr_ptr) {
                __builtin_dump_struct(expr_ptr, print_fn);
            }

            const struct_type2t &struct_type = to_struct_type(expr->type);
            json struct_data;
            
            std::cout << "DEBUG: Direct struct analysis:\n";
            std::cout << "  Members: " << struct_type.members.size() << "\n";
            
            for(size_t i = 0; i < struct_type.members.size(); i++) {
                const irep_idt& member_name = struct_type.member_names[i];
                const type2tc& member_type = struct_type.members[i];
                
                std::cout << "  Accessing member " << member_name << "\n";
                
                try {
                    expr2tc member_expr = member2tc(member_type, expr, member_name);
                    print_expr_info("member_expr", member_expr, ns);
                    struct_data[id2string(member_name)] = get_struct_values(ns, member_expr, depth + 1);
                } catch(const std::exception& e) {
                    std::cout << "  Error accessing member: " << e.what() << "\n";
                    struct_data[id2string(member_name)] = "access-error";
                }
            }
            return struct_data.dump();
        } catch(const std::exception& e) {
            std::cout << "DEBUG: Exception in struct analysis: " << e.what() << "\n";
            return "\"struct-access-failed\"";
        }
    }

    // Handle primitive types
    try {
        std::string val = from_expr(ns, "", expr);
        if(val.empty()) {
            return "\"\"";
        }

        // Try to parse as number first
        try {
            size_t pos;
            long long num = std::stoll(val, &pos);
            if(pos == val.length()) {
                return std::to_string(num);
            }
        } catch(...) {}

        return "\"" + val + "\"";
    } catch(...) {
        std::cout << "DEBUG: Exception getting primitive value\n";
        return "null";
    }
}

std::string get_assignment_message(const namespacet& ns, 
                                 const expr2tc& lhs, 
                                 const expr2tc& value) {
    std::string msg = from_expr(ns, "", lhs);
    
    if(is_nil_expr(value)) {
        return msg + " (assignment removed)";
    }
    
    msg += " = ";
    
    if(is_pointer_type(value->type) || is_struct_type(value->type)) {
        msg += get_struct_values(ns, value);
    } else {
        msg += from_expr(ns, "", value);
    }
    
    return msg;
}

void dump_type_info(const type2tc& type, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    std::cout << indent << "Type ID: " << get_type_id(type) << "\n";
    
    if(is_struct_type(type)) {
        const struct_type2t& struct_type = to_struct_type(type);
        std::cout << indent << "Struct with " << struct_type.members.size() << " members:\n";
        for(size_t i = 0; i < struct_type.members.size(); i++) {
            std::cout << indent << "  Member " << i << ": " << id2string(struct_type.member_names[i]) << "\n";
            dump_type_info(struct_type.members[i], ns, depth + 1);
        }
    }
    else if(is_pointer_type(type)) {
        const pointer_type2t& ptr_type = to_pointer_type(type);
        std::cout << indent << "Pointer to:\n";
        dump_type_info(ptr_type.subtype, ns, depth + 1);
    }
    else if(is_array_type(type)) {
        const array_type2t& arr_type = to_array_type(type);
        std::cout << indent << "Array of:\n";
        dump_type_info(arr_type.subtype, ns, depth + 1);
    }
}

void dump_value(const expr2tc& expr, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    if(is_nil_expr(expr)) {
        std::cout << indent << "<nil>\n";
        return;
    }

    // Dump the raw expression structure
    auto print_fn = [&indent](const char* fmt, ...) {
        va_list args;
        va_start(args, fmt);
        std::cout << indent << "Raw dump: ";
        vprintf(fmt, args);
        va_end(args);
    };
    
    const expr2t* expr_ptr = expr.get();
    if(expr_ptr) {
        __builtin_dump_struct(expr_ptr, print_fn);
    }

    // Try to get actual value based on type
    if(is_constant_int2t(expr)) {
        const constant_int2t& num = to_constant_int2t(expr);
        std::cout << indent << "Value: " << num.value << "\n";
    }
    else if(is_constant_string2t(expr)) {
        const constant_string2t& str = to_constant_string2t(expr);
        std::cout << indent << "Value: \"" << str.value << "\"\n";
    }
    else if(is_symbol2t(expr)) {
        const symbol2t& sym = to_symbol2t(expr);
        std::cout << indent << "Symbol: " << sym.thename << "\n";
        dump_type_info(sym.type, ns, depth + 1);
    }
}

void inspect_steps(const goto_tracet &trace, const namespacet &ns) {
    std::cout << "\nDEBUG Step inspection:\n";
    
    for(const auto &step : trace.steps) {
        if(step.is_assignment() && !is_nil_expr(step.lhs)) {
            std::cout << "\nDEBUG Assignment at " << step.pc->location << ":\n";
            
            // LHS analysis
            std::cout << "Left-hand side:\n";
            dump_value(step.lhs, ns, 1);
            
            // If it's a struct access or pointer dereference, try to get more info
            if(is_symbol2t(step.lhs)) {
                const symbol2t& sym = to_symbol2t(step.lhs);
                if(is_pointer_type(sym.type)) {
                    std::cout << "  Pointer details:\n";
                    const pointer_type2t& ptr = to_pointer_type(sym.type);
                    
                    // Try to dereference and get struct info
                    try {
                        expr2tc deref = dereference2tc(ptr.subtype, step.lhs);
                        std::cout << "  Dereferenced value:\n";
                        dump_value(deref, ns, 2);
                    } catch(const std::exception& e) {
                        std::cout << "  Cannot dereference: " << e.what() << "\n";
                    }
                }
            }
            
            // RHS/Value analysis
            if(!is_nil_expr(step.value)) {
                std::cout << "Right-hand side:\n";
                dump_value(step.value, ns, 1);
                
                // Try to get detailed value info
                if(is_struct_type(step.value->type)) {
                    std::cout << "  Struct value details:\n";
                    const struct_type2t& struct_type = to_struct_type(step.value->type);
                    for(size_t i = 0; i < struct_type.members.size(); i++) {
                        try {
                            expr2tc member = member2tc(
                                struct_type.members[i],
                                step.value,
                                struct_type.member_names[i]);
                                
                            std::cout << "    " << id2string(struct_type.member_names[i]) << ":\n";
                            dump_value(member, ns, 3);
                        } catch(const std::exception& e) {
                            std::cout << "    Cannot access member " 
                                     << id2string(struct_type.member_names[i])
                                     << ": " << e.what() << "\n";
                        }
                    }
                }
            }
        }
    }
}


void dump_struct_contents(const expr2tc& expr, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    
    if(is_nil_expr(expr)) {
        std::cout << indent << "<nil struct>\n";
        return;
    }

    // First try to dereference if it's a pointer
    expr2tc current_expr = expr;
    if(is_pointer_type(expr->type)) {
        try {
            current_expr = dereference2tc(expr->type, expr);
            std::cout << indent << "Dereferenced pointer successfully\n";
        } catch(const std::exception& e) {
            std::cout << indent << "Failed to dereference pointer: " << e.what() << "\n";
            return;
        }
    }

    // Now examine the struct contents
    if(is_struct_type(current_expr->type)) {
        const struct_type2t& struct_type = to_struct_type(current_expr->type);
        std::cout << indent << "Struct with " << struct_type.members.size() << " members:\n";

        for(size_t i = 0; i < struct_type.members.size(); i++) {
            const irep_idt& member_name = struct_type.member_names[i];
            const type2tc& member_type = struct_type.members[i];

            std::cout << indent << "Member " << i << ": " << id2string(member_name) << "\n";
            std::cout << indent << "  Type: " << get_type_id(member_type) << "\n";

            try {
                // Create member access expression
                expr2tc member_expr = member2tc(member_type, current_expr, member_name);
                
                // Get the actual value
                if(is_pointer_type(member_type)) {
                    std::cout << indent << "  Raw pointer value: " << from_expr(ns, "", member_expr) << "\n";
                    // Recursively inspect pointed-to struct
                    dump_struct_contents(member_expr, ns, depth + 1);
                } else {
                    std::string value = from_expr(ns, "", member_expr);
                    std::cout << indent << "  Value: " << value << "\n";
                }
            } catch(const std::exception& e) {
                std::cout << indent << "  Error accessing member: " << e.what() << "\n";
            }
        }
    }
}

void decode_struct_type(const type2tc& type, int depth = 0) {
    std::string indent(depth * 2, ' ');
    std::cout << indent << "Type decode: " << get_type_id(type) << "\n";
    
    if(is_struct_type(type)) {
        const struct_type2t& struct_type = to_struct_type(type);
        std::cout << indent << "Found struct with " << struct_type.members.size() << " members:\n";
        
        for(size_t i = 0; i < struct_type.members.size(); i++) {
            std::cout << indent << "  " << i << ": " << id2string(struct_type.member_names[i]) << "\n";
            decode_struct_type(struct_type.members[i], depth + 1);
        }
    }
    else if(is_array_type(type)) {
        const array_type2t& array_type = to_array_type(type);
        std::cout << indent << "Array of:\n";
        decode_struct_type(array_type.subtype, depth + 1);
    }
    else if(is_pointer_type(type)) {
        const pointer_type2t& ptr_type = to_pointer_type(type);
        std::cout << indent << "Pointer to:\n";
        decode_struct_type(ptr_type.subtype, depth + 1);
    }
}

void inspect_device_details(const expr2tc& expr, const namespacet& ns) {
    std::cout << "Starting detailed device inspection:\n";
    std::cout << "Expression ID: " << get_expr_id(expr) << "\n";
    std::cout << "Raw expr value: " << from_expr(ns, "", expr) << "\n";
    
    // First decode the type structure
    std::cout << "Type structure:\n";
    decode_struct_type(expr->type);
    
    // If it's a pointer type, try to dereference
    if(is_pointer_type(expr->type)) {
        const pointer_type2t& ptr_type = to_pointer_type(expr->type);
        
        std::cout << "Attempting to dereference device pointer:\n";
        try {
            expr2tc deref = dereference2tc(ptr_type.subtype, expr);
            std::cout << "Dereferenced successfully\n";
            
            // Get struct type from dereferenced expression
            if(is_struct_type(deref->type)) {
                const struct_type2t& struct_type = to_struct_type(deref->type);
                std::cout << "Device struct contents:\n";
                
                for(size_t i = 0; i < struct_type.members.size(); i++) {
                    const irep_idt& member_name = struct_type.member_names[i];
                    expr2tc member_expr = member2tc(struct_type.members[i], deref, member_name);
                    
                    std::cout << "  " << id2string(member_name) << " = ";
                    if(is_array_type(struct_type.members[i])) {
                        // Handle char arrays specially
                        std::cout << "[array data]\n";
                        dump_expr_recursive(member_expr, 2);
                    } else {
                        std::cout << from_expr(ns, "", member_expr) << "\n";
                    }
                }
            }
        } catch(const std::exception& e) {
            std::cout << "Dereference failed: " << e.what() << "\n";
        }
    }
    
    // Try to get the symbol type directly
    if(is_symbol2t(expr)) {
        const symbol2t& sym = to_symbol2t(expr);
        std::cout << "Symbol details:\n";
        std::cout << "  Name: " << sym.thename << "\n";
        
        // Convert dstring to std::string for manipulation
        std::string name_str = id2string(sym.thename);
        size_t last_at = name_str.find_last_of('@');
        if(last_at != std::string::npos) {
            std::string base_name = name_str.substr(last_at + 1);
            std::cout << "  Base name: " << base_name << "\n";
        }
        
        decode_struct_type(sym.type);
    }
}

// Helper function to examine expr details
void dump_expr_details(const expr2tc& expr, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    std::cout << indent << "Expression ID: " << get_expr_id(expr) << "\n";
    std::cout << indent << "Value: " << from_expr(ns, "", expr) << "\n";
    std::cout << indent << "Type ID: " << get_type_id(expr->type) << "\n";
}

// Helper to dump array data if possible
void try_dump_array(const expr2tc& array_expr, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    if(is_array_type(array_expr->type)) {
        const array_type2t& arr_type = to_array_type(array_expr->type);
        std::cout << indent << "Array of type: " << get_type_id(arr_type.subtype) << "\n";
        std::cout << indent << "Array value: " << from_expr(ns, "", array_expr) << "\n";
    }
}

// Approach 1: Using type system directly
void inspect_via_type_system(const expr2tc& expr, const namespacet& ns) {
    std::cout << "\nAPPROACH 1 - Type System Inspection:\n";
    
    if(is_nil_expr(expr)) {
        std::cout << "Nil expression\n";
        return;
    }

    dump_expr_details(expr, ns);
    
    // Walk the type hierarchy
    type2tc current_type = expr->type;
    while(!is_nil_type(current_type)) {
        std::cout << "Type level: " << get_type_id(current_type) << "\n";
        
        if(is_struct_type(current_type)) {
            const struct_type2t& struct_type = to_struct_type(current_type);
            std::cout << "Found struct with " << struct_type.members.size() << " members:\n";
            for(size_t i = 0; i < struct_type.members.size(); i++) {
                std::cout << "  Member " << i << ": " << id2string(struct_type.member_names[i]) << "\n";
                std::cout << "  Type: " << get_type_id(struct_type.members[i]) << "\n";
                
                // Try to get member value if this is DeviceRecord
                if(struct_type.members.size() == 6) { // DeviceRecord check
                    try {
                        expr2tc member = member2tc(struct_type.members[i], expr, struct_type.member_names[i]);
                        std::cout << "  Value: " << from_expr(ns, "", member) << "\n";
                    } catch(...) {
                        std::cout << "  Unable to get value\n";
                    }
                }
            }
        }
        else if(is_pointer_type(current_type)) {
            const pointer_type2t& ptr_type = to_pointer_type(current_type);
            std::cout << "Pointer to: " << get_type_id(ptr_type.subtype) << "\n";
            
            // Try to dereference and inspect content
            try {
                expr2tc deref = dereference2tc(current_type, expr);
                if(!is_nil_expr(deref)) {
                    std::cout << "Dereferenced content:\n";
                    dump_expr_details(deref, ns, 1);
                }
            } catch(...) {}
            
            current_type = ptr_type.subtype;
            continue;
        }
        break;
    }
}

// Approach 2: Using dereference and member access
void inspect_via_deref(const expr2tc& expr, const namespacet& ns) {
    std::cout << "\nAPPROACH 2 - Dereference Inspection:\n";
    
    if(is_pointer_type(expr->type)) {
        try {
            expr2tc deref = dereference2tc(expr->type, expr);
            std::cout << "Dereferenced value type: " << get_type_id(deref->type) << "\n";
            std::cout << "Dereferenced value: " << from_expr(ns, "", deref) << "\n";
            
            if(is_struct_type(deref->type)) {
                const struct_type2t& struct_type = to_struct_type(deref->type);
                if(struct_type.member_names.size() == 6) { // DeviceRecord check
                    std::cout << "DeviceRecord contents:\n";
                    for(size_t i = 0; i < struct_type.members.size(); i++) {
                        try {
                            expr2tc member = member2tc(struct_type.members[i], deref, struct_type.member_names[i]);
                            const std::string member_name = id2string(struct_type.member_names[i]);
                            std::string value = from_expr(ns, "", member);
                            
                            // Special handling for time_t if it's user_presence_exp
                            if(member_name == "user_presence_exp") {
                                if(is_constant_int2t(member)) {
                                    value = from_expr(ns, "", member);  // This already handles BigInt properly
                                }
                            }
                            
                            std::cout << "  " << member_name << " = " << value << "\n";
                        } catch(const std::exception& e) {
                            std::cout << "  Failed to access " << id2string(struct_type.member_names[i]) 
                                     << ": " << e.what() << "\n";
                        }
                    }
                }
            }
        } catch(const std::exception& e) {
            std::cout << "Dereference failed: " << e.what() << "\n";
        }
    }
}

// Approach 3: Using symbol resolution
void inspect_via_symbol(const expr2tc& expr, const namespacet& ns) {
    std::cout << "\nAPPROACH 3 - Symbol Resolution:\n";
    
    if(is_symbol2t(expr)) {
        const symbol2t& sym = to_symbol2t(expr);
        std::cout << "Symbol name: " << sym.thename << "\n";
        dump_expr_details(expr, ns, 1);
        
        try {
            // Try to get symbol info
            const symbolt* symbol = ns.lookup(sym.thename);
            if(symbol) {
                std::cout << "Found symbol in namespace\n";
                std::cout << "Symbol type: " << symbol->type.pretty() << "\n";
                std::cout << "Is struct: " << (symbol->type.is_struct() ? "yes" : "no") << "\n";
            }
        } catch(const std::exception& e) {
            std::cout << "Symbol lookup failed: " << e.what() << "\n";
        }
    }
}

// Approach 4: Raw struct memory examination
void inspect_memory(const expr2tc& expr, const namespacet& ns, int depth = 0) {
    std::string indent(depth * 2, ' ');
    std::cout << "\nAPPROACH 4 - Memory Examination:\n";
    
    const expr2t* raw_ptr = expr.get();
    std::cout << indent << "Expression at: " << (void*)raw_ptr << "\n";
    std::cout << indent << "Expression dump:\n";
    __builtin_dump_struct(raw_ptr, printf);
    
    if(const type2t* type_ptr = expr->type.get()) {
        std::cout << indent << "Type at: " << (void*)type_ptr << "\n";
        std::cout << indent << "Type dump:\n";
        __builtin_dump_struct(type_ptr, printf);
        
        if(is_pointer_type(expr->type)) {
            try {
                expr2tc deref = dereference2tc(expr->type, expr);
                if(!is_nil_expr(deref)) {
                    std::cout << indent << "Dereferenced content at: " 
                             << (void*)deref.get() << "\n";
                    std::cout << indent << "Dereferenced dump:\n";
                    __builtin_dump_struct(deref.get(), printf);
                }
            } catch(...) {
                std::cout << indent << "Failed to dereference\n";
            }
        }
    }
}

std::string extract_array_string(const expr2tc& array_expr) {
    // if(is_constant_array2t(array_expr)) {
    //     const constant_array2t& arr = to_constant_array2t(array_expr);
    //     std::string result;
    //     for(const auto& elem : arr.datatype_members) {
    //         if(is_constant_char2t(elem)) {
    //             char c = to_constant_char2t(elem).value;
    //             if(c != '\0') // Stop at null terminator
    //                 result += c;
    //         }
    //     }
    //     return result;
    // }
    return "<non-constant-array>";
}

void print_device_struct(const expr2tc& expr, const namespacet& ns) {
    try {
        json device_json;
        
        if(is_pointer_type(expr->type)) {
            expr2tc deref = dereference2tc(expr->type, expr);
            if(is_struct_type(deref->type)) {
                // print_struct(deref);
                // print_struct(deref);


                const struct_type2t& struct_type = to_struct_type(deref->type);
                
                for(size_t i = 0; i < struct_type.members.size(); i++) {
                    expr2tc member = member2tc(struct_type.members[i], deref, 
                                             struct_type.member_names[i]);
                    std::string member_name = id2string(struct_type.member_names[i]);
                    // print_struct(member);
                    
                    if(is_array_type(struct_type.members[i])) {
                        device_json[member_name] = extract_array_string(member);
                    } else {
                        device_json[member_name] = from_expr(ns, "", member);
                    }
                }
                
                std::cout << "Device contents:\n" 
                         << device_json.dump(2) << std::endl;
            }
        }
    } catch(const std::exception& e) {
        std::cout << "Failed to print device: " << e.what() << '\n';
    }
}

// Main inspection function that tries all approaches
void inspect_all_approaches(const expr2tc& expr, const namespacet& ns) {
    std::cout << "\n=== Trying all inspection approaches ===\n";
    print_device_struct(expr, ns);

    inspect_device_memory(expr, ns);

    inspect_via_type_system(expr, ns);
    inspect_via_deref(expr, ns);
    inspect_via_symbol(expr, ns);
    inspect_memory(expr, ns);
}

void track_variable_state(const goto_tracet &trace, const namespacet &ns) {
    std::cout << "\nDEBUG Tracking device state:\n";
    
    for(const auto &step : trace.steps) {
        if(!step.is_assignment())
            continue;
            
        std::string lhs_str = from_expr(ns, "", step.lhs);
        if(lhs_str.find("device") == 0 || lhs_str.find(".device") != std::string::npos) {
            std::cout << "\n=== DEVICE UPDATE at line " 
                     << step.pc->location.get_line() << " ===\n";
            
            std::cout << "LHS Expression: " << lhs_str << "\n";
            inspect_all_approaches(step.lhs, ns);
            
            if(!is_nil_expr(step.value)) {
                std::cout << "\nRHS Value:\n";
                inspect_all_approaches(step.value, ns);
            }
            
            // Try to get full struct for member updates
            if(is_member2t(step.lhs)) {
                std::cout << "\nParent struct:\n";
                inspect_all_approaches(to_member2t(step.lhs).source_value, ns);
            }
        }
    }
}

void add_coverage_to_json(const goto_tracet &goto_trace, const namespacet &ns) {
    json test_entry;
    test_entry["steps"] = json::array();
    test_entry["status"] = "unknown";
    test_entry["coverage"] = {{"files", json::object()}};
    
    // Add initial values tracking
    json initial_values = json::object();
    bool initial_state_captured = false;
    
    // Structure for tracking line hits
    std::map<std::string, std::map<int, int>> line_hits;
    std::set<std::pair<std::string, int>> violations;
    std::set<std::string> all_referenced_files;
    std::set<std::string> processed_files;
    std::set<std::string> processed_vars;
    
    size_t step_count = 0;
    bool found_violation = false;

    track_variable_state(goto_trace, ns);
    // inspect_steps(goto_trace, ns);

    // First pass - collect referenced files
    for(const auto &step : goto_trace.steps) {
        if(step.pc != goto_programt::const_targett() && !step.pc->location.is_nil()) {
            const locationt &loc = step.pc->location;
            std::string file = id2string(loc.get_file());
            
            if(!file.empty() && file.find("/usr/") != 0) {
                all_referenced_files.insert(file);
                auto included_headers = find_included_headers(file, processed_files);
                all_referenced_files.insert(included_headers.begin(), included_headers.end());
            }
        }
    }

    // Process all steps
    for(const auto &step : goto_trace.steps) {
        if(step.pc != goto_programt::const_targett() && !step.pc->location.is_nil()) {
            const locationt &loc = step.pc->location;
            std::string file = id2string(loc.get_file());
            
            if(file.find("/usr/") == 0) 
                continue;
            
            std::string line_str = id2string(loc.get_line());
            std::string function = id2string(loc.get_function());
            
            try {
                int line = std::stoi(line_str);
                
                if(line > 0) {
                    // Track line hits
                    line_hits[file][line]++;

                    json step_data;
                    step_data["file"] = file;
                    step_data["line"] = line_str;
                    step_data["function"] = function;
                    step_data["step_number"] = step_count++;

                    // Modified initial values capture
                    if(!initial_state_captured && step.is_assignment()) {
                        std::string var_name = from_expr(ns, "", step.lhs);
                        
                        if(processed_vars.find(var_name) == processed_vars.end()) {
                            processed_vars.insert(var_name);
                            
                            std::cout << "\nDEBUG Processing initial value for: " << var_name << "\n";
                            print_expr_info("step.lhs", step.lhs, ns);
                            print_expr_info("step.value", step.value, ns);
                            
                            try {
                                // Get all values recursively
                                std::string value = get_struct_values(ns, step.value);
                                std::cout << "DEBUG: Captured value: " << value << "\n";
                                
                                // Handle JSON parsing
                                try {
                                    json value_json = json::parse(value);
                                    initial_values[var_name] = value_json;
                                } catch(json::parse_error& e) {
                                    // If not valid JSON, store as string
                                    initial_values[var_name] = value;
                                }
                            } catch(std::exception& e) {
                                std::cout << "DEBUG: Error capturing value: " << e.what() << "\n";
                                initial_values[var_name] = "error-capturing-value";
                            }
                        }
                    }

                    // Handle different step types
                    if(step.is_assert()) {
                        if(!step.guard) {
                            violations.insert({file, line});
                            found_violation = true;
                            step_data["type"] = "violation";
                            step_data["message"] = step.comment.empty() ? "Assertion check" : step.comment;
                            test_entry["status"] = "violation";
                            step_data["assertion"] = {
                                {"violated", true},
                                {"comment", step.comment},
                                {"guard", from_expr(ns, "", step.pc->guard)}
                            };
                        } else {
                            step_data["type"] = "assert";
                        }
                    }
                    else if(step.is_assume()) {
                        step_data["type"] = "assume";
                        step_data["message"] = "Assumption restriction";
                    }
                    else if(step.is_assignment()) {
                        step_data["type"] = "assignment";
                        step_data["message"] = get_assignment_message(ns, step.lhs, step.value);
                    }
                    else if(step.pc->is_function_call()) {  // Changed from step.is_function_call()
                        step_data["type"] = "function_call";
                        step_data["message"] = fmt::format(
                            "Function argument '{}' = '{}'",
                            from_expr(ns, "", step.lhs),
                            from_expr(ns, "", step.value));
                    }
                    else {
                        step_data["type"] = "other";
                    }

                    test_entry["steps"].push_back(step_data);
                }
            } catch(std::exception& e) {
                std::cerr << "Error processing step: " << e.what() << std::endl;
                continue;
            }
        }
        
        // Mark initial state as captured after processing first few steps
        if(step_count > 3) {
            initial_state_captured = true;
        }
    }

    // Add initial values to test entry
    test_entry["initial_values"] = initial_values;

    // Set status if no violation found
    if(!found_violation && test_entry["status"] == "unknown") {
        test_entry["status"] = "success";
    }

    // Build coverage data
    for(const auto& file : all_referenced_files) {
        if(file.find("/usr/") == 0) 
            continue;
        
        json file_coverage;
        file_coverage["covered_lines"] = json::object();

        if(line_hits.find(file) != line_hits.end()) {
            for(const auto& [line, hits] : line_hits[file]) {
                std::string line_str = std::to_string(line);
                bool is_violation = violations.find({file, line}) != violations.end();

                file_coverage["covered_lines"][line_str] = {
                    {"covered", true},
                    {"hits", hits},
                    {"type", is_violation ? "violation" : "execution"}
                };
            }

            file_coverage["coverage_stats"] = {
                {"covered_lines", line_hits[file].size()},
                {"total_hits", std::accumulate(line_hits[file].begin(), line_hits[file].end(), 0,
                    [](int sum, const auto& p) { return sum + p.second; })}
            };
        } else {
            file_coverage["coverage_stats"] = {
                {"covered_lines", 0},
                {"total_hits", 0}
            };
        }

        test_entry["coverage"]["files"][file] = file_coverage;
    }

    // Handle source files tracking
    if(first_write) {
        for(const auto& file : all_referenced_files) {
            if(file.find("/usr/") == 0) 
                continue;
            
            if(source_files.find(file) == source_files.end()) {
                try {
                    const auto& file_lines = html_report::get_file_lines(file);
                    source_files[file] = std::vector<std::string>(file_lines.begin(), file_lines.end());
                } catch(std::exception& e) {
                    std::cerr << "Error reading file " << file << ": " << e.what() << std::endl;
                    source_files[file] = std::vector<std::string>();
                }
            }
        }
        
        json source_data;
        for(const auto& [file, lines] : source_files) {
            source_data[file] = lines;
        }
        test_entry["source_files"] = source_data;
    }

    // Read existing JSON if not first write
    json all_tests;
    if(!first_write) {
        std::ifstream input("report.json");
        if(input.is_open()) {
            try {
                input >> all_tests;
            } catch(json::parse_error& e) {
                std::cerr << "Error parsing existing report.json: " << e.what() << std::endl;
                all_tests = json::array();
            }
        } else {
            all_tests = json::array();
        }
    } else {
        all_tests = json::array();
    }

    // Append new test and write
    all_tests.push_back(test_entry);
    std::ofstream json_out("report.json");
    if(json_out.is_open()) {
        json_out << std::setw(2) << all_tests << std::endl;
        first_write = false;
    } else {
        std::cerr << "Error: Could not open report.json for writing" << std::endl;
    }
}

void generate_html_report(
  const std::string_view uuid,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const cmdlinet::options_mapt &options_map)
{
  log_status("Generating HTML report for trace: {}", uuid);
  const html_report report(goto_trace, ns, options_map);

  std::ofstream html(fmt::format("report-{}.html", uuid));
  report.output(html);
}

void generate_json_report(
  const std::string_view uuid,
  const namespacet &ns, 
  const goto_tracet &goto_trace,
  const cmdlinet::options_mapt &options_map)
{
  log_status("Generating JSON report for trace: {}", uuid);
  add_coverage_to_json(goto_trace, ns);
}