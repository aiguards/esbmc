#include <cassert>
#include <cstring>
#include <goto-symex/goto_trace.h>
#include <goto-symex/printf_formatter.h>
#include <goto-symex/witnesses.h>

#include <regex>
#include <langapi/language_util.h>
#include <langapi/languages.h>
#include <util/arith_tools.h>
#include <util/std_types.h>
#include <ostream>
#include <iomanip>
#include <fstream>
#include <stack>
#include <set>
#include <map>
#include <nlohmann/json.hpp>


using json = nlohmann::json;

void goto_tracet::output(const class namespacet &ns, std::ostream &out) const
{
  for (const auto &step : steps)
    step.output(ns, out);
}

void goto_trace_stept::dump() const
{
  std::ostringstream oss;
  output(*migrate_namespace_lookup, oss);
  log_debug("goto-trace", "{}", oss.str());
}

void goto_trace_stept::output(const namespacet &ns, std::ostream &out) const
{
  switch (type)
  {
  case goto_trace_stept::ASSERT:
    out << "ASSERT";
    break;

  case goto_trace_stept::ASSUME:
    out << "ASSUME";
    break;

  case goto_trace_stept::ASSIGNMENT:
    out << "ASSIGNMENT";
    break;

  default:
    assert(false);
  }

  if (type == ASSERT || type == ASSUME)
    out << " (" << guard << ")";

  out << "\n";

  if (!pc->location.is_nil())
    out << pc->location << "\n";

  if (pc->is_goto())
    out << "GOTO   ";
  else if (pc->is_assume())
    out << "ASSUME ";
  else if (pc->is_assert())
    out << "ASSERT ";
  else if (pc->is_other())
    out << "OTHER  ";
  else if (pc->is_assign())
    out << "ASSIGN ";
  else if (pc->is_function_call())
    out << "CALL   ";
  else
    out << "(?)    ";

  out << "\n";

  if (pc->is_other() || pc->is_assign())
  {
    irep_idt identifier;

    if (!is_nil_expr(original_lhs))
      identifier = to_symbol2t(original_lhs).get_symbol_name();
    else
      identifier = to_symbol2t(lhs).get_symbol_name();

    out << "  " << identifier << " = " << from_expr(ns, identifier, value)
        << "\n";
  }
  else if (pc->is_assert())
  {
    if (!guard)
    {
      out << "Violated property:"
          << "\n";
      if (pc->location.is_nil())
        out << "  " << pc->location << "\n";

      if (!comment.empty())
        out << "  " << comment << "\n";
      out << "  " << from_expr(ns, "", pc->guard) << "\n";
      out << "\n";
    }
  }

  out << "\n";
}

void counterexample_value(
  std::ostream &out,
  const namespacet &ns,
  const expr2tc &lhs,
  const expr2tc &value)
{
  out << "  " << from_expr(ns, "", lhs);
  if (is_nil_expr(value))
    out << "(assignment removed)";
  else
  {
    out << " = " << from_expr(ns, "", value);

    // Don't print the bit-vector if we're running on integer/real mode
    if (is_constant_expr(value) && !config.options.get_bool_option("ir"))
    {
      std::string binary_value = "";
      if (is_bv_type(value))
      {
        binary_value = integer2binary(
          to_constant_int2t(value).value, value->type->get_width());
      }
      else if (is_fixedbv_type(value))
      {
        binary_value =
          to_constant_fixedbv2t(value).value.to_expr().get_value().as_string();
      }
      else if (is_floatbv_type(value))
      {
        binary_value =
          to_constant_floatbv2t(value).value.to_expr().get_value().as_string();
      }

      if (!binary_value.empty())
      {
        out << " (";

        std::string::size_type i = 0;
        for (const auto c : binary_value)
        {
          out << c;
          if (++i % 8 == 0 && binary_value.size() != i)
            out << ' ';
        }

        out << ")";
      }
    }

    out << "\n";
  }
}

void show_goto_trace_gui(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  locationt previous_location;

  for (const auto &step : goto_trace.steps)
  {
    const locationt &location = step.pc->location;

    if ((step.type == goto_trace_stept::ASSERT) && !step.guard)
    {
      out << "FAILED"
          << "\n"
          << step.comment << "\n" // value
          << "\n"                 // PC
          << location.file() << "\n"
          << location.line() << "\n"
          << location.column() << "\n";
    }
    else if (step.type == goto_trace_stept::ASSIGNMENT)
    {
      irep_idt identifier;

      if (!is_nil_expr(step.original_lhs))
        identifier = to_symbol2t(step.original_lhs).get_symbol_name();
      else
        identifier = to_symbol2t(step.lhs).get_symbol_name();

      std::string value_string = from_expr(ns, identifier, step.value);

      const symbolt *symbol = ns.lookup(identifier);
      irep_idt base_name;
      if (symbol)
        base_name = symbol->name;

      out << "TRACE"
          << "\n";

      out << identifier << "," << base_name << ","
          << get_type_id(step.value->type) << "," << value_string << "\n"
          << step.step_nr << "\n"
          << step.pc->location.file() << "\n"
          << step.pc->location.line() << "\n"
          << step.pc->location.column() << "\n";
    }
    else if (location != previous_location)
    {
      // just the location

      if (!location.file().empty())
      {
        out << "TRACE"
            << "\n";

        out << "," // identifier
            << "," // base_name
            << "," // type
            << ""
            << "\n" // value
            << step.step_nr << "\n"
            << location.file() << "\n"
            << location.line() << "\n"
            << location.column() << "\n";
      }
    }

    previous_location = location;
  }
}

void show_state_header(
  std::ostream &out,
  const goto_trace_stept &state,
  const locationt &location,
  unsigned step_nr)
{
  out << "\n";
  out << "State " << step_nr;
  out << " " << location << " thread " << state.thread_nr << "\n";
  out << "----------------------------------------------------"
      << "\n";
}

void violation_graphml_goto_trace(
  optionst &options,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  grapht graph(grapht::VIOLATION);
  graph.verified_file = options.get_option("input-file");

  log_progress("Generating Violation Witness for: {}", graph.verified_file);

  edget *first_edge = &graph.edges.at(0);
  nodet *prev_node = first_edge->to_node;

  for (const auto &step : goto_trace.steps)
  {
    switch (step.type)
    {
    case goto_trace_stept::ASSERT:
      if (!step.guard)
      {
        graph.check_create_new_thread(step.thread_nr, prev_node);
        prev_node = graph.edges.back().to_node;

        nodet *violation_node = new nodet();
        violation_node->violation = true;

        edget violation_edge(prev_node, violation_node);
        violation_edge.thread_id = std::to_string(step.thread_nr);
        violation_edge.start_line = get_line_number(
          graph.verified_file,
          std::atoi(step.pc->location.get_line().c_str()),
          options);

        graph.edges.push_back(violation_edge);

        /* having printed a property violation, don't print more steps. */

        graph.generate_graphml(options);
        return;
      }
      break;

    case goto_trace_stept::ASSIGNMENT:
      if (
        step.pc->is_assign() || step.pc->is_return() ||
        (step.pc->is_other() && is_nil_expr(step.lhs)) ||
        step.pc->is_function_call())
      {
        std::string assignment = get_formated_assignment(ns, step);

        graph.check_create_new_thread(step.thread_nr, prev_node);
        prev_node = graph.edges.back().to_node;

        edget new_edge;
        new_edge.thread_id = std::to_string(step.thread_nr);
        new_edge.assumption = assignment;
        new_edge.start_line = get_line_number(
          graph.verified_file,
          std::atoi(step.pc->location.get_line().c_str()),
          options);

        nodet *new_node = new nodet();
        new_edge.from_node = prev_node;
        new_edge.to_node = new_node;
        prev_node = new_node;
        graph.edges.push_back(new_edge);
      }
      break;

    default:
      continue;
    }
  }
}

void correctness_graphml_goto_trace(
  optionst &options,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  grapht graph(grapht::CORRECTNESS);
  graph.verified_file = options.get_option("input-file");
  log_progress("Generating Correctness Witness for: {}", graph.verified_file);

  edget *first_edge = &graph.edges.at(0);
  nodet *prev_node = first_edge->to_node;

  for (const auto &step : goto_trace.steps)
  {
    /* checking restrictions for correctness GraphML */
    if (
      (!(is_valid_witness_step(ns, step))) ||
      (!(step.is_assume() || step.is_assert())))
      continue;

    std::string invariant = get_invariant(
      graph.verified_file,
      std::atoi(step.pc->location.get_line().c_str()),
      options);

    if (invariant.empty())
      continue; /* we don't have to consider this invariant */

    nodet *new_node = new nodet();
    edget *new_edge = new edget();
    std::string function = step.pc->location.get_function().c_str();
    new_edge->start_line = get_line_number(
      graph.verified_file,
      std::atoi(step.pc->location.get_line().c_str()),
      options);
    new_node->invariant = invariant;
    new_node->invariant_scope = function;

    new_edge->from_node = prev_node;
    new_edge->to_node = new_node;
    prev_node = new_node;
    graph.edges.push_back(*new_edge);
  }

  graph.generate_graphml(options);
}

void show_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  using json = nlohmann::json;
  
  try {
    // Print counterexample header first if there are any steps
    if (!goto_trace.steps.empty()) {
      out << "\n[Counterexample]\n";
    }
    
    json test_data;
    test_data["steps"] = json::array();
    test_data["status"] = "unknown";
    test_data["coverage"] = {
      {"files", json::object()},
      {"functions", json::object()},
      {"overall_stats", json::object()}
    };

    bool found_violation = false;
    
    // First collect all files and try to read their contents
    std::map<std::string, std::vector<std::string>> source_files;
    std::map<std::string, std::map<std::string, std::pair<int, int>>> function_bounds;
    std::set<std::string> processed_files;
    
    for (const auto &step : goto_trace.steps) {
      if (!step.pc->location.is_nil()) {
        std::string file = step.pc->location.get_file().as_string();
        std::string function = step.pc->location.get_function().as_string();
        
        if (!file.empty() && processed_files.find(file) == processed_files.end()) {
          processed_files.insert(file);
          std::ifstream source_file(file);
          if (source_file.is_open()) {
            std::vector<std::string> lines;
            std::string line;
            int line_num = 1;
            bool in_function = false;
            std::string current_function;
            int function_start = 0;
            int brace_count = 0;
            
            while (std::getline(source_file, line)) {
              lines.push_back(line);
              
              // More robust function boundary detection
              if (line.find(function + "(") != std::string::npos && 
                  line.find(";") == std::string::npos) {  // Function definition
                in_function = true;
                current_function = function;
                function_start = line_num;
                brace_count = 0;
              }
              
              // Count braces for better function end detection
              if (in_function) {
                for (char c : line) {
                  if (c == '{') brace_count++;
                  if (c == '}') brace_count--;
                }
                
                if (brace_count == 0 && function_start != line_num) {
                  // End of function
                  if (function_bounds[file].find(current_function) == function_bounds[file].end()) {
                    function_bounds[file][current_function] = std::make_pair(function_start, line_num);
                  }
                  in_function = false;
                }
              }
              line_num++;
            }
            source_files[file] = lines;
          }
        }
      }
    }
    
    // Initialize coverage data with file contents
    for (const auto& [file, lines] : source_files) {
      test_data["coverage"]["files"][file] = {
        {"total_lines", lines.size()},
        {"source", lines},
        {"covered_lines", json::object()},
        {"functions", json::object()},
        {"all_lines", json::array()}
      };
      
      // Initialize all possible lines
      for (size_t i = 0; i < lines.size(); i++) {
        test_data["coverage"]["files"][file]["all_lines"].push_back(i + 1);
      }
      
      // Initialize function boundaries
      for (const auto& [func_name, bounds] : function_bounds[file]) {
        test_data["coverage"]["files"][file]["functions"][func_name] = {
          {"bounds", {
            {"start_line", bounds.first},
            {"end_line", bounds.second}
          }},
          {"covered_lines", json::object()},
          {"hits", 0}
        };
      }
    }
    
    // Process trace steps
    for (const auto &step : goto_trace.steps) {
      json step_data;
      
      if (!step.pc->location.is_nil()) {
        std::string file = step.pc->location.get_file().as_string();
        std::string line = step.pc->location.get_line().as_string();
        std::string function = step.pc->location.get_function().as_string();
        
        step_data["file"] = file;
        step_data["line"] = line;
        step_data["function"] = function;
        
        if (!file.empty() && !line.empty()) {
          auto& file_coverage = test_data["coverage"]["files"][file];
          
          // Track line coverage
          if (!file_coverage["covered_lines"].contains(line)) {
            file_coverage["covered_lines"][line] = {
              {"hits", 1},
              {"function", function},
              {"covered", true},
              {"step_type", std::to_string(step.type)}
            };
          } else {
            file_coverage["covered_lines"][line]["hits"] = 
              file_coverage["covered_lines"][line]["hits"].get<int>() + 1;
          }
          
          // Track function coverage
          if (!function.empty() && file_coverage["functions"].contains(function)) {
            auto& func_data = file_coverage["functions"][function];
            func_data["hits"] = func_data["hits"].get<int>() + 1;
            func_data["covered_lines"][line] = true;
          }
        }
        
        switch(step.type) {
          case goto_trace_stept::ASSERT:
            if(!step.guard) {
              found_violation = true;
              out << "Violated property:\n";
              if(!step.pc->location.is_nil()) {
                out << "  " << step.pc->location << "\n";
              }
              if(!step.comment.empty()) 
                out << "  " << step.comment << "\n";
              if(step.pc->is_assert())
                out << "  " << from_expr(ns, "", step.pc->guard) << "\n";
              
              step_data["assertion"] = {
                {"violated", true},
                {"comment", step.comment},
                {"guard", from_expr(ns, "", step.pc->guard)}
              };
            } else {
              step_data["assertion"] = {
                {"violated", false},
                {"guard", from_expr(ns, "", step.pc->guard)}
              };
            }
            break;

          case goto_trace_stept::ASSIGNMENT:
            if(!is_nil_expr(step.lhs) && is_symbol2t(step.lhs)) {
              const symbol2t &symbol = to_symbol2t(step.lhs);
              out << "  " << symbol.thename 
                  << " = " << from_expr(ns, "", step.value) << "\n";
              
              step_data["assignment"] = {
                {"variable", symbol.thename.as_string()},
                {"value", from_expr(ns, "", step.value)}
              };
            }
            break;

          case goto_trace_stept::OUTPUT:
            if(!step.output_args.empty()) {
              printf_formattert printf_formatter;
              printf_formatter(step.format_string, step.output_args);
              std::ostringstream oss;
              printf_formatter.print(oss);
              out << "  " << oss.str() << "\n";
              
              step_data["output"] = oss.str();
            }
            break;

          case goto_trace_stept::ASSUME:
            step_data["assume"] = {
              {"condition", from_expr(ns, "", step.pc->guard)}
            };
            break;

          default:
            step_data["type"] = "other";
            break;
        }
      }
      
      test_data["steps"].push_back(step_data);
    }
    
    // Set final status
    test_data["status"] = found_violation ? "violation" : "success";
    
    // Calculate coverage statistics
    size_t total_covered = 0;
    size_t total_lines = 0;
    
    for (auto& [file, file_data] : test_data["coverage"]["files"].items()) {
      // Get actual function lines for more accurate coverage
      std::set<int> function_lines;
      for (const auto& [func_name, func_data] : file_data["functions"].items()) {
        int start = func_data["bounds"]["start_line"].get<int>();
        int end = func_data["bounds"]["end_line"].get<int>();
        for (int i = start; i <= end; i++) {
          function_lines.insert(i);
        }
      }
      
      json uncovered_lines = json::array();
      json covered_lines = json::array();
      
      for (int line : function_lines) {
        std::string line_str = std::to_string(line);
        if (file_data["covered_lines"].contains(line_str)) {
          covered_lines.push_back(line);
        } else {
          uncovered_lines.push_back(line);
        }
      }
      
      file_data["uncovered_lines"] = uncovered_lines;
      file_data["covered_lines_list"] = covered_lines;
      
      size_t covered_count = file_data["covered_lines"].size();
      total_covered += covered_count;
      total_lines += function_lines.size();
      
      double coverage_percent = function_lines.size() > 0 ? 
        (static_cast<double>(covered_count) * 100.0) / static_cast<double>(function_lines.size()) : 0.0;
      
      file_data["coverage_stats"] = {
        {"total_lines", file_data["total_lines"]},
        {"function_lines", function_lines.size()},
        {"covered_lines", covered_count},
        {"coverage_percentage", coverage_percent}
      };
      
      // Calculate function-level coverage
      for (auto& [func_name, func_data] : file_data["functions"].items()) {
        int func_start = func_data["bounds"]["start_line"].get<int>();
        int func_end = func_data["bounds"]["end_line"].get<int>();
        size_t func_total_lines = func_end - func_start + 1;
        size_t func_covered_lines = func_data["covered_lines"].size();
        
        std::vector<int> func_uncovered;
        for (int i = func_start; i <= func_end; i++) {
          if (!func_data["covered_lines"].contains(std::to_string(i))) {
            func_uncovered.push_back(i);
          }
        }
        
        func_data["uncovered_lines"] = func_uncovered;
        func_data["coverage_stats"] = {
          {"total_lines", func_total_lines},
          {"covered_lines", func_covered_lines},
          {"coverage_percentage", func_total_lines > 0 ?
            (static_cast<double>(func_covered_lines) * 100.0) / static_cast<double>(func_total_lines) : 0.0}
        };
      }
    }
    
    // Add overall statistics
    test_data["coverage"]["overall_stats"] = {
      {"total_files", test_data["coverage"]["files"].size()},
      {"total_lines", total_lines},
      {"total_covered_lines", total_covered},
      {"overall_coverage_percentage", total_lines > 0 ?
        (static_cast<double>(total_covered) * 100.0) / static_cast<double>(total_lines) : 0.0}
    };
    
    std::ofstream json_out("tests.json");
    json_out << std::setw(2) << test_data << std::endl;
    
  } catch (const std::exception& e) {
    out << "Error: " << e.what() << "\n";
  } catch (...) {
    out << "Unknown error occurred\n";
  }
}

// End of file