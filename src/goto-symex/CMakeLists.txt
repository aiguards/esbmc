# First find libdwarf
find_package(PkgConfig REQUIRED)
pkg_check_modules(DWARF REQUIRED libdwarf)
find_library(ELF_LIBRARY elf)
if(ELF_LIBRARY)
    target_link_libraries(symex ${ELF_LIBRARY})
endif()

add_library(symex symex_target.cpp symex_target_equation.cpp symex_assign.cpp
  symex_main.cpp  symex_stack.cpp goto_trace.cpp build_goto_trace.cpp
  symex_function.cpp goto_symex_state.cpp symex_dereference.cpp symex_goto.cpp
  builtin_functions.cpp slice.cpp symex_other.cpp xml_goto_trace.cpp
  symex_valid_object.cpp dynamic_allocation.cpp symex_catch.cpp renaming.cpp
  execution_state.cpp reachability_tree.cpp reachability_tree_cin.cpp
  witnesses.cpp printf_formatter.cpp features.cpp html.cpp)
target_include_directories(symex
    PRIVATE ${CMAKE_BINARY_DIR}/src
    PRIVATE ${Boost_INCLUDE_DIRS}
    PRIVATE ${DWARF_INCLUDE_DIRS}  # Add this line
)
target_link_libraries(symex dwarf nlohmann_json::nlohmann_json fmt::fmt     ${DWARF_LIBRARIES})

if(WIN32)
  target_link_libraries(symex nlohmann_json::nlohmann_json fmt::fmt wsock32 ws2_32)
endif()
