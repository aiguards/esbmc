#include <goto-programs/assign_params_as_non_det.h>

bool assign_params_as_non_det::runOnFunction(
  std::pair<const dstring, goto_functiont> &F)
{
  if (context.find_symbol(F.first) == nullptr)
    return false; // Not exist

  exprt symbol = symbol_expr(*context.find_symbol(F.first));

  if (!symbol.type().is_code())
    return false; // Not expected
  code_typet t = to_code_type(symbol.type());

  if (symbol.name().as_string() != target_function)
    return false; // Not target function

  if (!F.second.body_available)
    return false; // Empty function

  goto_programt &goto_program = F.second.body;
  auto it = (goto_program).instructions.begin();
  locationt l = context.find_symbol(F.first)->location;

  for (const auto &arg : t.arguments())
  {
    // lhs
    const auto &_id = arg.get("#identifier");
    if (context.find_symbol(_id) == nullptr)
      return false; // Not expected
    exprt lhs = symbol_expr(*context.find_symbol(_id));

    if (lhs.type().is_pointer())
    {
      // get subType()
      typet subt = lhs.type().subtype();
      
      // create obj and move it to the symbol table
      symbolt s;
      s.name = "obj_" + id2string(_id); 
      s.type = subt;
      s.location = l;
      context.move(s);

      // Create nondet bool condition
      exprt nondet_bool = symbol_expr(*context.find_symbol("c:@F@nondet_bool"));

      // Create assignment: lhs = &obj
      code_assignt assign(lhs, address_of_exprt(symbol_expr(s)));
      assign.location() = l;

      // Add to goto program
      goto_programt tmp;
      goto_programt::targett t = tmp.add_instruction(GOTO);
      t->location = l;
      t->function = it->location.get_function();
      migrate_expr(nondet_bool, t->guard);

      goto_programt::targett assign_instr = tmp.add_instruction(ASSIGN);
      assign_instr->location = l;
      assign_instr->function = it->location.get_function();
      migrate_expr(assign, assign_instr->code);

      // insert both instructions
      goto_program.insert_swap(it++, *t);
      goto_program.insert_swap(it++, *assign_instr);
      --it;
    }
    else
    {
      // rhs
      exprt rhs = exprt("sideeffect", lhs.type());
      rhs.statement("nondet");
      rhs.location() = l;

      // assignment
      goto_programt tmp;
      goto_programt::targett assignment = tmp.add_instruction(ASSIGN);
      assignment->location = l;
      assignment->function = it->location.get_function();

      code_assignt code_assign(lhs, rhs);
      code_assign.location() = it->location;
      migrate_expr(code_assign, assignment->code);

      // insert
      goto_program.insert_swap(it++, *assignment);
      --it;
    }
  }

  goto_program.update();
  return true;
}

//End of file