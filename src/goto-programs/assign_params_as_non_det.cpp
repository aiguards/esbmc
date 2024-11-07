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
      // e.g. int* lhs;

      // get subType() => int
      typet subt = lhs.type().subtype();

      // create obj and move it to the symbol table
      symbolt s;
      s.name = "obj_" + id2string(_id);
      s.type = subt;
      s.location = l;
      context.move(s);

      // create decl statement => int obj_(id);
      code_declt _decl(symbol_expr(s));
      ;

      // create a goto_instructiont DECL and insert to the original program  => DECL obj_(id)
      goto_programt tmp;
      goto_programt::targett decl_statement = tmp.add_instruction(DECL);
      decl_statement->location = l;
      decl_statement->function = it->location.get_function();
      migrate_expr(_decl, decl_statement->code);

      // insert
      goto_program.insert_swap(it++, *decl_statement);
      --it;

      // do assignment => lhs = &obj_(id)
      code_assignt assign(lhs, address_of_exprt(symbol_expr(s)));
      assign.location() = l;
      codet if_body;
      if_body.make_block();
      if_body.move_to_operands(assign);

      // create if statement => if(nondet_bool()) lhs = &obj_(id);

      exprt _non_det = symbol_expr(*context.find_symbol("c:@F@nondet_bool"));
      codet _non_det_code("expression");
      _non_det_code.location() = l;
      _non_det_code.move_to_operands(_non_det);

      codet if_code("ifthenelse");
      if_code.copy_to_operands(_non_det_code, if_body);

      // inser if statement to the goto program
      goto_programt tmp2;
      goto_programt::targett if_statement = tmp2.add_instruction(GOTO);
      if_statement->location = l;
      if_statement->function = it->location.get_function();
      migrate_expr(if_code, if_statement->code);

      // insert
      goto_program.insert_swap(it++, *if_statement);
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