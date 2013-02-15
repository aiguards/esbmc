#include <sstream>

#include "smt_conv.h"

// Helpers extracted from z3_convt.

static std::string
extract_magnitude(std::string v, unsigned width)
{
    return integer2string(binary2integer(v.substr(0, width / 2), true), 10);
}

static std::string
extract_fraction(std::string v, unsigned width)
{
    return integer2string(binary2integer(v.substr(width / 2, width), false), 10);
}

static unsigned int
get_member_name_field(const type2tc &t, const irep_idt &name)
{
  unsigned int idx = 0;
  const struct_union_data &data_ref =
          dynamic_cast<const struct_union_data &>(*t);

  forall_names(it, data_ref.member_names) {
    if (*it == name)
      break;
    idx++;
  }
  assert(idx != data_ref.member_names.size() &&
         "Member name of with expr not found in struct/union type");

  return idx;
}

static unsigned int
get_member_name_field(const type2tc &t, const expr2tc &name)
{
  const constant_string2t &str = to_constant_string2t(name);
  return get_member_name_field(t, str.value);
}

smt_convt::smt_convt(bool enable_cache, bool intmode, const namespacet &_ns,
                     bool is_cpp)
  : caching(enable_cache), int_encoding(intmode), ns(_ns)
{
  std::vector<type2tc> members;
  std::vector<irep_idt> names;

  members.push_back(type_pool.get_uint(config.ansi_c.pointer_width));
  members.push_back(type_pool.get_uint(config.ansi_c.pointer_width));
  names.push_back(irep_idt("pointer_object"));
  names.push_back(irep_idt("pointer_offset"));

  struct_type2t *tmp = new struct_type2t(members, names, "pointer_struct");
  pointer_type_data = tmp;
  pointer_struct = type2tc(tmp);

  pointer_logic.push_back(pointer_logict());

  addr_space_sym_num.push_back(0);

  members.clear();
  names.clear();
  members.push_back(type_pool.get_uint(config.ansi_c.pointer_width));
  members.push_back(type_pool.get_uint(config.ansi_c.pointer_width));
  names.push_back(irep_idt("start"));
  names.push_back(irep_idt("end"));
  tmp = new struct_type2t(members, names, "addr_space_type");
  addr_space_type_data = tmp;
  addr_space_type = type2tc(tmp);

  addr_space_arr_type = type2tc(new array_type2t(addr_space_type,
                                                 expr2tc(), true)) ;

  addr_space_data.push_back(std::map<unsigned, unsigned>());

  // Pick a modelling array to shoehorn initialization data into. Because
  // we don't yet have complete data for whether pointers are dynamic or not,
  // this is the one modelling array that absolutely _has_ to be initialized
  // to false for each element, which is going to be shoved into
  // convert_identifier_pointer.
  if (is_cpp) {
    dyn_info_arr_name = "cpp::__ESBMC_is_dynamic&0#1";
  } else {
    dyn_info_arr_name = "c::__ESBMC_is_dynamic&0#1";
  }
}

smt_convt::~smt_convt(void)
{
}

void
smt_convt::push_ctx(void)
{
  addr_space_data.push_back(addr_space_data.back());
  addr_space_sym_num.push_back(addr_space_sym_num.back());
  pointer_logic.push_back(pointer_logic.back());
  prop_convt::push_ctx();
}

void
smt_convt::pop_ctx(void)
{
  prop_convt::pop_ctx();

  union_varst::nth_index<1>::type &union_numindex = union_vars.get<1>();
  union_numindex.erase(ctx_level);
  smt_cachet::nth_index<1>::type &cache_numindex = smt_cache.get<1>();
  cache_numindex.erase(ctx_level);
  pointer_logic.pop_back();
  addr_space_sym_num.pop_back();
  addr_space_data.pop_back();
}

void
smt_convt::set_to(const expr2tc &expr, bool value)
{

  l_set_to(convert(expr), value);

  // Workaround for the fact that we don't have a good way of encoding unions
  // into SMT. Just work out what the last assigned field is.
  if (is_equality2t(expr) && value) {
    const equality2t eq = to_equality2t(expr);
    if (is_union_type(eq.side_1->type) && is_with2t(eq.side_2)) {
      const symbol2t sym = to_symbol2t(eq.side_1);
      const with2t with = to_with2t(eq.side_2);
      const union_type2t &type = to_union_type(eq.side_1->type);
      const std::string &ref = sym.get_symbol_name();
      const constant_string2t &str = to_constant_string2t(with.update_field);

      unsigned int idx = 0;
      forall_names(it, type.member_names) {
        if (*it == str.value)
          break;
        idx++;
      }

      assert(idx != type.member_names.size() &&
             "Member name of with expr not found in struct/union type");

      union_var_mapt mapentry = { ref, idx, 0 };
      union_vars.insert(mapentry);
    }
  }
}

literalt
smt_convt::convert_expr(const expr2tc &expr)
{
  const smt_ast *a = convert_ast(expr);
  return mk_lit(a);
}

const smt_ast *
smt_convt::convert_ast(const expr2tc &expr)
{
  const smt_ast *args[4];
  const smt_sort *sort;
  const smt_ast *a;
  unsigned int num_args, used_sorts = 0;

  if (caching) {
    smt_cachet::const_iterator cache_result = smt_cache.find(expr);
    if (cache_result != smt_cache.end())
      return (cache_result->ast);
  }

  // Convert /all the arguments/.
  unsigned int i = 0;
  forall_operands2(it, idx, expr) {
    args[i] = convert_ast(*it);
    used_sorts |= args[i]->sort->id;
    i++;
  }
  num_args = i;

  sort = convert_sort(expr->type);

  const expr_op_convert *cvt = &smt_convert_table[expr->expr_id];

  if ((int_encoding && cvt->int_mode_func > SMT_FUNC_INVALID) ||
      (!int_encoding && cvt->bv_mode_func_signed > SMT_FUNC_INVALID)) {
    assert(cvt->args == num_args);
    // An obvious check, but catches cases where we add a field to a future expr
    // and then fail to update the SMT layer, leading to an ignored field.

    // Now check sort types.
    if ((used_sorts | cvt->permitted_sorts) == cvt->permitted_sorts) {
      // Matches; we can just convert this.
      smt_func_kind k = (int_encoding) ? cvt->int_mode_func
                      : (is_signedbv_type(expr->type))
                          ? cvt->bv_mode_func_signed
                          : cvt->bv_mode_func_unsigned;
      a = mk_func_app(sort, k, &args[0], cvt->args, expr);
      goto done;
    }
  }

  if ((int_encoding && cvt->int_mode_func == SMT_FUNC_INVALID) ||
      (!int_encoding && cvt->bv_mode_func_signed == SMT_FUNC_INVALID)) {
    std::cerr << "Invalid expression " << get_expr_id(expr) << " for encoding "
      << "mode discovered, refusing to convert to SMT" << std::endl;
    abort();
  }

  switch (expr->expr_id) {
  case expr2t::constant_int_id:
  case expr2t::constant_fixedbv_id:
  case expr2t::constant_bool_id:
  case expr2t::symbol_id:
    a = convert_terminal(expr);
    break;
  case expr2t::add_id:
  case expr2t::sub_id:
  {
    a = convert_pointer_arith(expr, expr->type);
    break;
  }
  case expr2t::mul_id:
  {
    assert(!is_fixedbv_type(expr) && "haven't got SMT backend supporting fixedbv mul yet");
    assert(0);
  }
  case expr2t::div_id:
  {
    assert(!is_fixedbv_type(expr) && "haven't got SMT backend supporting fixedbv div yet");
    assert(0);
  }
  case expr2t::with_id:
  {
    // We reach here if we're with'ing a struct, not an array.
    assert(is_struct_type(expr->type));
    const with2t &with = to_with2t(expr);
    unsigned int idx = get_member_name_field(expr->type, with.update_field);
    a = tuple_update(args[0], idx, args[2], expr);
    break;
  }
  case expr2t::member_id:
  {
    const smt_sort *sort = convert_sort(expr->type);
    const member2t &memb = to_member2t(expr);
    unsigned int idx = get_member_name_field(memb.source_value->type, memb.member);
    a = tuple_project(args[0], sort, idx, expr);
    break;
  }
  case expr2t::same_object_id:
  {
    // Two projects, then comparison.
    smt_sort *s = convert_sort(pointer_type_data->members[0]);
    args[0] = tuple_project(args[0], s, 0, expr2tc());
    args[1] = tuple_project(args[1], s, 0, expr2tc());
    a = mk_func_app(sort, SMT_FUNC_EQ, &args[0], 2, expr);
    break;
  }
  case expr2t::pointer_offset_id:
  {
    smt_sort *s = convert_sort(pointer_type_data->members[1]);
    a = tuple_project(args[0], s, 1, expr);
    break;
  }
  case expr2t::pointer_object_id:
  {
    smt_sort *s = convert_sort(pointer_type_data->members[0]);
    a = tuple_project(args[0], s, 0, expr);
    break;
  }
  default:
    a = mk_func_app(sort, SMT_FUNC_HACKS, &args[0], 0, expr);
    break;
  }

done:
  struct smt_cache_entryt entry = { expr, a, ctx_level };
  smt_cache.insert(entry);
  return a;
}

void
smt_convt::assert_expr(const expr2tc &e)
{
  const smt_ast *a = convert_ast(e);
  literalt l = mk_lit(a);
  assert_lit(l);
  return;
}

smt_sort *
smt_convt::convert_sort(const type2tc &type)
{
  bool is_signed = true;

  switch (type->type_id) {
  case type2t::bool_id:
    return mk_sort(SMT_SORT_BOOL);
  case type2t::struct_id:
    return mk_struct_sort(type);
  case type2t::union_id:
    return mk_union_sort(type);
  case type2t::pointer_id:
    return mk_struct_sort(pointer_struct);
  case type2t::unsignedbv_id:
    is_signed = false;
    /* FALLTHROUGH */
  case type2t::signedbv_id:
  {
    unsigned int width = type->get_width();
    if (int_encoding)
      return mk_sort(SMT_SORT_INT, is_signed);
    else
      return mk_sort(SMT_SORT_BV, width, is_signed);
  }
  case type2t::fixedbv_id:
  {
    unsigned int width = type->get_width();
    if (int_encoding)
      return mk_sort(SMT_SORT_REAL);
    else
      return mk_sort(SMT_SORT_BV, width, false);
  }
  case type2t::string_id:
  {
    smt_sort *d = (int_encoding)? mk_sort(SMT_SORT_INT)
                                : mk_sort(SMT_SORT_BV, config.ansi_c.int_width,
                                          !config.ansi_c.char_is_unsigned);
    smt_sort *r = (int_encoding)? mk_sort(SMT_SORT_INT)
                                : mk_sort(SMT_SORT_BV, 8,
                                          !config.ansi_c.char_is_unsigned);
    return mk_sort(SMT_SORT_ARRAY, d, r);
  }
  case type2t::array_id:
  {
    // All arrays are indexed by integerse
    smt_sort *d = (int_encoding)? mk_sort(SMT_SORT_INT)
                                : mk_sort(SMT_SORT_BV, config.ansi_c.int_width,
                                          false);
    const array_type2t &arr = to_array_type(type);
    smt_sort *r = convert_sort(arr.subtype);
    return mk_sort(SMT_SORT_ARRAY, d, r);
  }
  case type2t::code_id:
  case type2t::cpp_name_id:
  case type2t::symbol_id:
  case type2t::empty_id:
  default:
    assert(0 && "Unexpected type ID reached SMT conversion");
  }
}

smt_ast *
smt_convt::convert_terminal(const expr2tc &expr)
{
  switch (expr->expr_id) {
  case expr2t::constant_int_id:
  {
    bool sign = is_signedbv_type(expr);
    const constant_int2t &theint = to_constant_int2t(expr);
    unsigned int width = expr->type->get_width();
    if (int_encoding)
      return mk_smt_int(theint.constant_value, sign, expr);
    else
      return mk_smt_bvint(theint.constant_value, sign, width, expr);
  }
  case expr2t::constant_fixedbv_id:
  {
    const constant_fixedbv2t &thereal = to_constant_fixedbv2t(expr);
    if (int_encoding) {
      return mk_smt_real(thereal.value.to_integer(), expr);
    } else {
      assert(thereal.type->get_width() <= 64 && "Converting fixedbv constant to"
             " SMT, too large to fit into a uint64_t");

      uint64_t magnitude, fraction, fin;
      unsigned int bitwidth = thereal.type->get_width();
      std::string m, f, c;
      std::string theval = thereal.value.to_expr().value().as_string();

      m = extract_magnitude(theval, bitwidth);
      f = extract_fraction(theval, bitwidth);
      magnitude = atoi(m.c_str());
      fraction = atoi(f.c_str());

      magnitude <<= (bitwidth / 2);
      fin = magnitude | fraction;

      return mk_smt_bvint(mp_integer(fin), false, bitwidth, expr);
    }
  }
  case expr2t::constant_bool_id:
  {
    const constant_bool2t &thebool = to_constant_bool2t(expr);
    return mk_smt_bool(thebool.constant_value, expr);
  }
  case expr2t::symbol_id:
  {
    // Can't do this right now due to not having sort conversion yet.
    const symbol2t &sym = to_symbol2t(expr);
    std::string name = sym.get_symbol_name();
    const smt_sort *sort = convert_sort(sym.type);
    return mk_smt_symbol(name, sort, expr);
  }
  default:
    return mk_func_app(NULL, SMT_FUNC_HACKS, NULL, 0, expr);
  }
}

smt_ast *
smt_convt::tuple_create(const expr2tc &structdef __attribute__((unused)))
{
  assert(0);
}

smt_ast *
smt_convt::tuple_project(const smt_ast *a __attribute__((unused)),
                         const smt_sort *s __attribute__((unused)),
                         unsigned int i __attribute__((unused)),
                         const expr2tc &tmp __attribute__((unused)))
{
  assert(0);
}

smt_ast *
smt_convt::tuple_update(const smt_ast *a __attribute__((unused)),
                        unsigned int i __attribute__((unused)),
                        const smt_ast *v __attribute__((unused)),
                        const expr2tc &tmp __attribute__((unused)))
{
  assert(0);
}

smt_ast *
smt_convt::tuple_equality(const smt_ast *a __attribute__((unused)),
                          const smt_ast *b __attribute__((unused)),
                          const expr2tc &tmp __attribute__((unused)))
{
  assert(0);
}

const smt_ast *
smt_convt::convert_pointer_arith(const expr2tc &expr, const type2tc &type)
{
  const arith_2ops &expr_ref = static_cast<const arith_2ops &>(*expr);
  const expr2tc &side1 = expr_ref.side_1;
  const expr2tc &side2 = expr_ref.side_2;

  // So eight cases; one for each combination of two operands and the return
  // type, being pointer or nonpointer. So with P=pointer, N= notpointer,
  //    return    op1        op2        action
  //      N        N          N         Will never be fed here
  //      N        P          N         Expected arith option, then cast to int
  //      N        N          P            "
  //      N        P          P         Not permitted by C spec
  //      P        N          N         Return arith action with cast to pointer
  //      P        P          N         Calculate expected ptr arith operation
  //      P        N          P            "
  //      P        P          P         Not permitted by C spec
  //      NPP is the most dangerous - there's the possibility that an integer
  //      arithmatic is going to lead to an invalid pointer, that falls out of
  //      all dereference switch cases. So, we need to verify that all derefs
  //      have a finally case that asserts the val was a valid ptr XXXjmorse.
  int ret_is_ptr, op1_is_ptr, op2_is_ptr;
  ret_is_ptr = (is_pointer_type(type)) ? 4 : 0;
  op1_is_ptr = (is_pointer_type(side1)) ? 2 : 0;
  op2_is_ptr = (is_pointer_type(side2)) ? 1 : 0;

  switch (ret_is_ptr | op1_is_ptr | op2_is_ptr) {
    case 0:
      assert(false);
      break;
    case 3:
    case 7:
      assert(0 && "Pointer arithmetic with two pointer operands");
      break;
    case 4:
      // Artithmetic operation that has the result type of ptr.
      // Should have been handled at a higher level
      assert(0 && "Non-pointer op being interpreted as pointer without cast");
      break;
    case 1:
    case 2:
      { // Block required to give a variable lifetime to the cast/add variables
      expr2tc ptr_op = (op1_is_ptr) ? side1 : side2;
      expr2tc non_ptr_op = (op1_is_ptr) ? side2 : side1;

      add2tc add(ptr_op->type, ptr_op, non_ptr_op);
      // That'll generate the correct pointer arithmatic; now typecast
      typecast2tc cast(type, add);
      return convert_ast(cast);
      }
    case 5:
    case 6:
      {
      expr2tc ptr_op = (op1_is_ptr) ? side1 : side2;
      expr2tc non_ptr_op = (op1_is_ptr) ? side2 : side1;

      // Actually perform some pointer arith
      const pointer_type2t &ptr_type = to_pointer_type(ptr_op->type);
      typet followed_type_old = ns.follow(migrate_type_back(ptr_type.subtype));
      type2tc followed_type;
      migrate_type(followed_type_old, followed_type);
      mp_integer type_size = pointer_offset_size(*followed_type);

      // Generate nonptr * constant.
      type2tc inttype(new unsignedbv_type2t(config.ansi_c.int_width));
      constant_int2tc constant(get_uint_type(32), type_size);
      expr2tc mul = mul2tc(inttype, non_ptr_op, constant);

      // Add or sub that value
      expr2tc ptr_offset = pointer_offset2tc(inttype, ptr_op);

      expr2tc newexpr;
      if (is_add2t(expr)) {
        newexpr = add2tc(inttype, mul, ptr_offset);
      } else {
        // Preserve order for subtraction.
        expr2tc tmp_op1 = (op1_is_ptr) ? ptr_offset : mul;
        expr2tc tmp_op2 = (op1_is_ptr) ? mul : ptr_offset;
        newexpr = sub2tc(inttype, tmp_op1, tmp_op2);
      }

      // Voila, we have our pointer arithmatic
      const smt_ast *a = convert_ast(newexpr);
      const smt_ast *the_ptr = convert_ast(ptr_op);

      // That calculated the offset; update field in pointer.
      return tuple_update(the_ptr, 1, a, expr);
      }
  }

  assert(0 && "Fell through convert_pointer_logic");
}

const smt_ast *
smt_convt::convert_identifier_pointer(const expr2tc &expr, std::string symbol)
{
  const smt_ast *a;
  const smt_sort *s;
  std::string cte, identifier;
  unsigned int obj_num;
  bool got_obj_num = false;

  if (is_symbol2t(expr)) {
    const symbol2t &sym = to_symbol2t(expr);
    if (sym.thename == "NULL" || sym.thename == "0") {
      obj_num = pointer_logic.back().get_null_object();
      got_obj_num = true;
    }
  }

  if (!got_obj_num)
    // add object won't duplicate objs for identical exprs (it's a map)
    obj_num = pointer_logic.back().add_object(expr);

  s = convert_sort(pointer_struct);
  a = mk_smt_symbol(symbol, s, expr);

  // If this object hasn't yet been put in the address space record, we need to
  // assert that the symbol has the object ID we've allocated, and then fill out
  // the address space record.
  if (addr_space_data.back().find(obj_num) == addr_space_data.back().end()) {

    std::vector<expr2tc> membs;
    membs.push_back(gen_uint(obj_num));
    membs.push_back(zero_uint);
    constant_struct2tc ptr_val_s(pointer_struct, membs);
    const smt_ast *ptr_val = tuple_create(ptr_val_s);
    const smt_ast *constraint = tuple_equality(a, ptr_val, expr);
    literalt l = mk_lit(constraint);
    assert_lit(l);

    type2tc ptr_loc_type(new unsignedbv_type2t(config.ansi_c.int_width));

    std::stringstream sse1, sse2;
    sse1 << "__ESBMC_ptr_obj_start_" << obj_num;
    sse2 << "__ESBMC_ptr_obj_end_" << obj_num;
    std::string start_name = sse1.str();
    std::string end_name = sse2.str();

    symbol2tc start_sym(ptr_loc_type, start_name);
    symbol2tc end_sym(ptr_loc_type, end_name);

    // Another thing to note is that the end var must be /the size of the obj/
    // from start. Express this in irep.
    expr2tc endisequal;
    try {
      uint64_t type_size = expr->type->get_width() / 8;
      constant_int2tc const_offs(ptr_loc_type, BigInt(type_size));
      add2tc start_plus_offs(ptr_loc_type, start_sym, const_offs);
      endisequal = equality2tc(start_plus_offs, end_sym);
    } catch (array_type2t::dyn_sized_array_excp *e) {
      // Dynamically (nondet) sized array; take that size and use it for the
      // offset-to-end expression.
      const expr2tc size_expr = e->size;
      add2tc start_plus_offs(ptr_loc_type, start_sym, size_expr);
      endisequal = equality2tc(start_plus_offs, end_sym);
    } catch (type2t::symbolic_type_excp *e) {
      // Type is empty or code -- something that we can never have a real size
      // for. In that case, create an object of size 1: this means we have a
      // valid entry in the address map, but that any modification of the
      // pointer leads to invalidness, because there's no size to think about.
      constant_int2tc const_offs(ptr_loc_type, BigInt(1));
      add2tc start_plus_offs(ptr_loc_type, start_sym, const_offs);
      endisequal = equality2tc(start_plus_offs, end_sym);
    }

    // Assert that start + offs == end
    assert_expr(endisequal);

    // Even better, if we're operating in bitvector mode, it's possible that
    // the solver will try to be clever and arrange the pointer range to cross
    // the end of the address space (ie, wrap around). So, also assert that
    // end > start
    greaterthan2tc wraparound(end_sym, start_sym);
    assert_expr(wraparound);

    // Generate address space layout constraints.
    finalize_pointer_chain(obj_num);

    addr_space_data.back()[obj_num] =
          pointer_offset_size(*expr->type.get()).to_long() + 1;

    membs.clear();
    membs.push_back(start_sym);
    membs.push_back(end_sym);
    constant_struct2tc range_struct(addr_space_type, membs);
    std::stringstream ss;
    ss << "__ESBMC_ptr_addr_range_" <<  obj_num;
    symbol2tc range_sym(addr_space_type, ss.str());
    equality2tc eq(range_sym, range_struct);
    assert_expr(eq);

    // Update array
    bump_addrspace_array(obj_num, range_struct);

    // Finally, ensure that the array storing whether this pointer is dynamic,
    // is initialized for this ptr to false. That way, only pointers created
    // through malloc will be marked dynamic.

    type2tc arrtype(new array_type2t(type2tc(new bool_type2t()),
                                     expr2tc((expr2t*)NULL), true));
    symbol2tc allocarr(arrtype, dyn_info_arr_name);
    constant_int2tc objid(get_uint_type(config.ansi_c.int_width),
                          BigInt(obj_num));
    index2tc idx(get_bool_type(), allocarr, objid);
    equality2tc dyn_eq(idx, false_expr);
    assert_expr(dyn_eq);
  }

  return a;
}

void
smt_convt::finalize_pointer_chain(unsigned int objnum)
{
  type2tc inttype = get_uint_type(config.ansi_c.int_width);
  unsigned int num_ptrs = addr_space_data.back().size();
  if (num_ptrs == 0)
    return;

  std::stringstream start1, end1;
  start1 << "__ESBMC_ptr_obj_start_" << objnum;
  end1 << "__ESBMC_ptr_obj_end_" << objnum;
  symbol2tc start_i(inttype, start1.str());
  symbol2tc end_i(inttype, end1.str());

  for (unsigned int j = 0; j < objnum; j++) {
    // Obj1 is designed to overlap
    if (j == 1)
      continue;

    std::stringstream startj, endj;
    startj << "__ESBMC_ptr_obj_start_" << j;
    endj << "__ESBMC_ptr_obj_end_" << j;
    symbol2tc start_j(inttype, startj.str());
    symbol2tc end_j(inttype, endj.str());

    // Formula: (i_end < j_start) || (i_start > j_end)
    // Previous assertions ensure start < end for all objs.
    lessthan2tc lt1(end_i, start_j);
    greaterthan2tc gt1(start_i, end_j);
    or2tc or1(lt1, gt1);
    assert_expr(or1);
  }

  return;
}

const smt_ast *
smt_convt::convert_addr_of(const expr2tc &expr)
{
  const address_of2t &obj = to_address_of2t(expr);

  std::string symbol_name, out;

  if (is_index2t(obj.ptr_obj)) {
    const index2t &idx = to_index2t(obj.ptr_obj);

    if (!is_string_type(idx.source_value)) {
      const array_type2t &arr = to_array_type(idx.source_value->type);

      // Pick pointer-to array subtype; need to make pointer arith work.
      address_of2tc addrof(arr.subtype, idx.source_value);
      add2tc plus(addrof->type, addrof, idx.index);
      return convert_ast(plus);
    } else {
      // Strings; convert with slightly different types.
      type2tc stringtype(new unsignedbv_type2t(8));
      address_of2tc addrof(stringtype, idx.source_value);
      add2tc plus(addrof->type, addrof, idx.index);
      convert_ast(plus);
    }
  } else if (is_member2t(obj.ptr_obj)) {
    const member2t &memb = to_member2t(obj.ptr_obj);

    int64_t offs;
    if (is_struct_type(memb.source_value)) {
      const struct_type2t &type = to_struct_type(memb.source_value->type);
      offs = member_offset(type, memb.member).to_long();
    } else {
      offs = 0; // Offset is always zero for unions.
    }

    address_of2tc addr(type2tc(new pointer_type2t(memb.source_value->type)),
                       memb.source_value);

    const smt_ast *a = convert_ast(addr);

    // Update pointer offset to offset to that field.
    constant_int2tc offset(get_int_type(config.ansi_c.int_width), BigInt(offs));
    const smt_ast *o = convert_ast(offset);
    return tuple_update(a, 1, o, expr);
  } else if (is_symbol2t(obj.ptr_obj)) {
// XXXjmorse             obj.ptr_obj->expr_id == expr2t::code_id) {

    const symbol2t &symbol = to_symbol2t(obj.ptr_obj);
    return convert_identifier_pointer(obj.ptr_obj, symbol.get_symbol_name());
  } else if (is_constant_string2t(obj.ptr_obj)) {
    // XXXjmorse - we should avoid encoding invalid characters in the symbol,
    // but this works for now.
    const constant_string2t &str = to_constant_string2t(obj.ptr_obj);
    std::string identifier =
      "address_of_str_const(" + str.value.as_string() + ")";
    return convert_identifier_pointer(obj.ptr_obj, identifier);
  } else if (is_if2t(obj.ptr_obj)) {
    // We can't nondeterministically take the address of something; So instead
    // rewrite this to be if (cond) ? &a : &b;.

    const if2t &ifval = to_if2t(obj.ptr_obj);

    address_of2tc addrof1(obj.type, ifval.true_value);
    address_of2tc addrof2(obj.type, ifval.false_value);
    if2tc newif(obj.type, ifval.cond, addrof1, addrof2);
    return convert_ast(newif);
  } else if (is_typecast2t(obj.ptr_obj)) {
    // Take the address of whatevers being casted. Either way, they all end up
    // being of a pointer_tuple type, so this should be fine.
    address_of2tc tmp(type2tc(), to_typecast2t(obj.ptr_obj).from);
    tmp.get()->type = obj.type;
    return convert_ast(tmp);
  }

  assert(0 && "Unrecognized address_of operand");
}

void
smt_convt::init_addr_space_array(void)
{
  addr_space_sym_num.back() = 1;

  type2tc ptr_int_type = get_uint_type(config.ansi_c.pointer_width);
  symbol2tc obj0_start(ptr_int_type, "__ESBMC_ptr_obj_start_0");
  symbol2tc obj0_end(ptr_int_type, "__ESBMC_ptr_obj_start_0");
  equality2tc obj0_start_eq(obj0_start, zero_uint);
  equality2tc obj0_end_eq(obj0_start, zero_uint);

  assert_expr(obj0_start_eq);
  assert_expr(obj0_end_eq);

  symbol2tc obj1_start(ptr_int_type, "__ESBMC_ptr_obj_start_1");
  symbol2tc obj1_end(ptr_int_type, "__ESBMC_ptr_obj_start_1");
  constant_int2tc obj1_end_const(ptr_int_type, BigInt(0xFFFFFFFFFFFFFFFFULL));
  equality2tc obj1_start_eq(obj1_start, one_uint);
  equality2tc obj1_end_eq(obj1_end, obj1_end_const);

  assert_expr(obj1_start_eq);
  assert_expr(obj1_end_eq);

  std::vector<expr2tc> membs;
  membs.push_back(obj0_start);
  membs.push_back(obj0_start);
  constant_struct2tc addr0_tuple(addr_space_type, membs);
  symbol2tc addr0_range(addr_space_type, "__ESBMC_ptr_addr_range_0");
  equality2tc addr0_range_eq(addr0_tuple, addr0_range);
  assert_expr(addr0_range_eq);

  membs.clear();
  membs.push_back(obj1_start);
  membs.push_back(obj1_end);
  constant_struct2tc addr1_tuple(addr_space_type, membs);
  symbol2tc addr1_range(addr_space_type, "__ESBMC_ptr_addr_range_1");
  equality2tc addr1_range_eq(addr1_tuple, addr1_range);
  assert_expr(addr1_range_eq);

  bump_addrspace_array(pointer_logic.back().get_null_object(), addr0_tuple);
  bump_addrspace_array(pointer_logic.back().get_invalid_object(), addr1_tuple);

  // Give value to '0', 'NULL', 'INVALID' symbols
  symbol2tc zero_ptr(pointer_struct, "0");
  symbol2tc null_ptr(pointer_struct, "NULL");
  symbol2tc invalid_ptr(pointer_struct, "INVALID");

  membs.clear();
  membs.push_back(zero_uint);
  membs.push_back(zero_uint);
  constant_struct2tc null_ptr_tuple(pointer_struct, membs);
  membs.clear();
  membs.push_back(one_uint);
  membs.push_back(zero_uint);
  constant_struct2tc invalid_ptr_tuple(pointer_struct, membs);

  equality2tc zero_eq(zero_ptr, null_ptr_tuple);
  equality2tc null_eq(null_ptr, null_ptr_tuple);
  equality2tc invalid_eq(invalid_ptr, invalid_ptr_tuple);

  assert_expr(zero_eq);
  assert_expr(null_eq);
  assert_expr(invalid_eq);
}


void
smt_convt::bump_addrspace_array(unsigned int idx, const expr2tc &val)
{
  std::stringstream ss, ss2;
  std::string str, new_str;
  type2tc ptr_int_type = get_uint_type(config.ansi_c.pointer_width);

  ss2 << "__ESBMC_addrspace_arr_" << addr_space_sym_num.back()++;
  symbol2tc oldname(addr_space_arr_type, ss2.str());
  constant_int2tc ptr_idx(ptr_int_type, BigInt(idx));

  with2tc store(addr_space_arr_type, oldname, ptr_idx, val);
  ss2 << "__ESBMC_addrspace_arr_" << addr_space_sym_num.back();
  symbol2tc newname(addr_space_arr_type, ss2.str());
  equality2tc eq(newname, store);
  assert_expr(eq);
  return;
}

std::string
smt_convt::get_cur_addrspace_ident(void)
{
  std::stringstream ss;
  ss << "__ESBMC_addrspace_arr_" << addr_space_sym_num.back();
  return ss.str();
}

const smt_ast *
smt_convt::convert_sign_ext(const smt_ast *a, const smt_sort *s,
                            unsigned int topbit, unsigned int topwidth)
{
  const smt_ast *args[4];

  const smt_sort *bit = mk_sort(SMT_SORT_BV, 1, false);
  args[0] = mk_extract(a, topbit-1, topbit-2, bit, expr2tc());
  args[1] = mk_smt_bvint(BigInt(0), false, 1, expr2tc());
  const smt_sort *b = mk_sort(SMT_SORT_BOOL);
  const smt_ast *t = mk_func_app(b, SMT_FUNC_EQ, args, 2, expr2tc());

  const smt_ast *z = mk_smt_bvint(BigInt(0), false, topwidth, expr2tc());
  const smt_ast *f = mk_smt_bvint(BigInt(0xFFFFFFFFFFFFFFFFULL), false,
                                  topwidth, expr2tc());

  args[0] = t;
  args[1] = z;
  args[2] = f;
  const smt_sort *topsort = mk_sort(SMT_SORT_BV, topwidth, false);
  const smt_ast *topbits = mk_func_app(topsort, SMT_FUNC_ITE, args, 3,
                                       expr2tc());

  args[0] = topbits;
  args[1] = a;
  return mk_func_app(s, SMT_FUNC_CONCAT, args, 2, expr2tc());
}

const smt_ast *
smt_convt::convert_zero_ext(const smt_ast *a, const smt_sort *s,
                            unsigned int topwidth)
{
  const smt_ast *args[2];

  const smt_ast *z = mk_smt_bvint(BigInt(0), false, topwidth, expr2tc());
  args[0] = z;
  args[1] = a;
  return mk_func_app(s, SMT_FUNC_CONCAT, args, 2, expr2tc());
}

const smt_ast *
smt_convt::convert_typecast_bool(const typecast2t &cast)
{

  if (is_bv_type(cast.from)) {
    notequal2tc neq(cast.from, zero_uint);
    return convert_ast(neq);
  } else if (is_pointer_type(cast.from)) {
    // Convert to two casts.
    typecast2tc to_int(get_uint_type(config.ansi_c.pointer_width), cast.from);
    constant_int2tc zero(get_uint_type(config.ansi_c.pointer_width), BigInt(0));
    equality2tc as_bool(zero, to_int);
    return convert_ast(as_bool);
  } else {
    assert(0 && "Unimplemented bool typecast");
  }
}

const smt_ast *
smt_convt::convert_typecast_fixedbv_nonint(const expr2tc &expr)
{
  const smt_ast *args[4];
  const typecast2t &cast = to_typecast2t(expr);
  const fixedbv_type2t &fbvt = to_fixedbv_type(cast.type);
  unsigned to_fraction_bits = fbvt.width - fbvt.integer_bits;
  unsigned to_integer_bits = fbvt.integer_bits;

  if (is_pointer_type(cast.from)) {
    std::cerr << "Converting pointer to a float is unsupported" << std::endl;
    abort();
  }

  const smt_ast *a = convert_ast(cast.from);
  const smt_sort *s = convert_sort(cast.type);

  if (is_bv_type(cast.from)) {
    unsigned from_width = cast.from->type->get_width();

    if (from_width == to_integer_bits) {
      ; // No-op, already converted by higher caller
      return a;
    } else if (from_width > to_integer_bits) {
      const smt_sort *tmp = mk_sort(SMT_SORT_BV, from_width - to_integer_bits,
                                    false);
      args[0] = mk_extract(a, (from_width - 1), to_integer_bits, tmp, expr);
    } else {
      assert(from_width < to_integer_bits);
      const smt_sort *tmp = mk_sort(SMT_SORT_BV, to_integer_bits, false);
      args[0] = convert_sign_ext(a, tmp, from_width,
                                 to_integer_bits - from_width);
    }

    // Make all zeros fraction bits
    args[1] = mk_smt_bvint(BigInt(0), false, to_fraction_bits, expr2tc());
    return mk_func_app(s, SMT_FUNC_CONCAT, args, 2, expr);
  } else if (is_bool_type(cast.from)) {
    const smt_ast *args[3];
    const smt_sort *intsort;
    args[0] = a;
    args[1] = mk_smt_bvint(BigInt(0), false, to_integer_bits, expr2tc());
    args[2] = mk_smt_bvint(BigInt(1), false, to_integer_bits, expr2tc());
    intsort = mk_sort(SMT_SORT_BV, to_integer_bits, false);
    args[0] = mk_func_app(intsort, SMT_FUNC_ITE, args, 3, expr2tc());
    args[1] = mk_smt_bvint(BigInt(0), false, to_integer_bits, expr2tc());
    return mk_func_app(s, SMT_FUNC_CONCAT, args, 2, expr);
  } else if (is_fixedbv_type(cast.from)) {
    const smt_ast *magnitude, *fraction;

    const fixedbv_type2t &from_fbvt = to_fixedbv_type(cast.from->type);

    unsigned from_fraction_bits = from_fbvt.width - from_fbvt.integer_bits;
    unsigned from_integer_bits = from_fbvt.integer_bits;
    unsigned from_width = from_fbvt.width;

    if (to_integer_bits <= from_integer_bits) {
      const smt_sort *tmp_sort = mk_sort(SMT_SORT_BV, to_integer_bits, false);
      magnitude = mk_extract(a, (from_fraction_bits + to_integer_bits - 1),
                             from_fraction_bits, tmp_sort, expr2tc());
    } else   {
      assert(to_integer_bits > from_integer_bits);
      const smt_sort *tmp_sort = mk_sort(SMT_SORT_BV,
                                        from_width - from_fraction_bits, false);
      const smt_ast *ext = mk_extract(a, from_width - 1, from_fraction_bits,
                                      tmp_sort, expr2tc());

      tmp_sort = mk_sort(SMT_SORT_BV, (from_width - from_fraction_bits)
                                      + (to_integer_bits - from_integer_bits),
                                      false);
      magnitude = convert_sign_ext(ext, tmp_sort,
                                   from_width - from_fraction_bits,
                                   to_integer_bits - from_integer_bits);
    }

    if (to_fraction_bits <= from_fraction_bits) {
      const smt_sort *tmp_sort = mk_sort(SMT_SORT_BV, to_fraction_bits, false);
      fraction = mk_extract(a, from_fraction_bits - 1,
                            from_fraction_bits - to_fraction_bits, tmp_sort,
                            expr2tc());
    } else {
      const smt_ast *args[2];
      assert(to_fraction_bits > from_fraction_bits);
      const smt_sort *tmp_sort = mk_sort(SMT_SORT_BV, from_fraction_bits,
                                         false);
      args[0] = mk_extract(a, from_fraction_bits -1, 0, tmp_sort, expr2tc());
      args[1] = mk_smt_bvint(BigInt(0), false,
                             to_fraction_bits - from_fraction_bits,
                             expr2tc());

      tmp_sort = mk_sort(SMT_SORT_BV, to_fraction_bits, false);
      fraction = mk_func_app(tmp_sort, SMT_FUNC_CONCAT, args, 2, expr2tc());
    }

    const smt_ast *args[2];
    args[0] = magnitude;
    args[1] = fraction;
    return mk_func_app(s, SMT_FUNC_CONCAT, args, 2, expr);
  }

  std::cerr << "unexpected typecast to fixedbv" << std::endl;
  abort();
}

const smt_ast *
smt_convt::convert_typecast_to_ints(const typecast2t &cast)
{
  unsigned to_width = cast.type->get_width();
  const smt_sort *s = convert_sort(cast.type);
  const smt_ast *a = convert_ast(cast.from);

  if (is_signedbv_type(cast.from) || is_fixedbv_type(cast.from)) {
    unsigned from_width = cast.from->type->get_width();

    if (from_width == to_width) {
      if (int_encoding && is_signedbv_type(cast.from) &&
               is_fixedbv_type(cast.type)) {
        return mk_func_app(s, SMT_FUNC_INT2REAL, &a, 1, expr2tc());
      } else if (int_encoding && is_fixedbv_type(cast.from) &&
               is_signedbv_type(cast.type)) {
        return mk_func_app(s, SMT_FUNC_REAL2INT, &a, 1, expr2tc());
      }
      // XXXjmorse - there isn't a case here for if !int_encoding
    } else if (from_width < to_width) {
      if (int_encoding &&
          ((is_fixedbv_type(cast.type) && is_signedbv_type(cast.from)))) {
        return mk_func_app(s, SMT_FUNC_INT2REAL, &a, 1, expr2tc());
      } else if (int_encoding) {
	return a; // output = output
      } else {
        return convert_sign_ext(a, s, from_width, (to_width - from_width));
      }
    } else if (from_width > to_width) {
      if (int_encoding &&
          ((is_signedbv_type(cast.from) && is_fixedbv_type(cast.type)))) {
        return mk_func_app(s, SMT_FUNC_INT2REAL, &a, 1, expr2tc());
      } else if (int_encoding &&
                (is_fixedbv_type(cast.from) && is_signedbv_type(cast.type))) {
        return mk_func_app(s, SMT_FUNC_REAL2INT, &a, 1, expr2tc());
      } else if (int_encoding) {
        return a; // output = output
      } else {
	if (!to_width)
          to_width = config.ansi_c.int_width;

        return mk_extract(a, to_width-1, 0, s, expr2tc());
      }
    }
  } else if (is_unsignedbv_type(cast.from)) {
    unsigned from_width = cast.from->type->get_width();

    if (from_width == to_width) {
      return a; // output = output
    } else if (from_width < to_width) {
      if (int_encoding) {
	return a; // output = output
      } else {
        return convert_zero_ext(a, s, (to_width - from_width));
      }
    } else if (from_width > to_width) {
      if (int_encoding) {
	return a; // output = output
      } else {
        return mk_extract(a, to_width - 1, 0, s, expr2tc());
      }
    }
  } else if (is_bool_type(cast.from)) {
    const smt_ast *zero, *one;
    unsigned width = cast.type->get_width();

    if (is_bv_type(cast.type)) {
      zero = mk_smt_bvint(BigInt(0), false, width, expr2tc());
      one = mk_smt_bvint(BigInt(1), false, width, expr2tc());
    } else if (is_fixedbv_type(cast.type)) {
      zero = mk_smt_real(BigInt(0), expr2tc());
      one = mk_smt_real(BigInt(1), expr2tc());
    } else {
      std::cerr << "Unexpected type in typecast of bool" << std::endl;
      abort();
    }

    const smt_ast *args[3];
    args[0] = a;
    args[1] = one;
    args[2] = zero;
    return mk_func_app(s, SMT_FUNC_ITE, args, 3, expr2tc());
  }

  std::cerr << "Unexpected type in int/ptr typecast" << std::endl;
  abort();
}

const smt_ast *
smt_convt::convert_typecast_to_ptr(const typecast2t &cast)
{

  // First, sanity check -- typecast from one kind of a pointer to another kind
  // is a simple operation. Check for that first.
  if (is_pointer_type(cast.from)) {
    return convert_ast(cast.from);
  }

  // Unpleasentness; we don't know what pointer this integer is going to
  // correspond to, and there's no way of telling statically, so we have
  // to enumerate all pointers it could point at. IE, all of them. Which
  // is expensive, but here we are.

  // First cast it to an unsignedbv
  type2tc int_type = get_uint_type(config.ansi_c.int_width);
  typecast2tc cast_to_unsigned(int_type, cast.from);
  expr2tc target = cast_to_unsigned;

  // Construct array for all possible object outcomes
  expr2tc is_in_range[addr_space_data.back().size()];
  expr2tc obj_ids[addr_space_data.back().size()];
  expr2tc obj_starts[addr_space_data.back().size()];

  std::map<unsigned,unsigned>::const_iterator it;
  unsigned int i;
  for (it = addr_space_data.back().begin(), i = 0;
       it != addr_space_data.back().end(); it++, i++)
  {
    unsigned id = it->first;
    obj_ids[i] = constant_int2tc(int_type, BigInt(id));

    std::stringstream ss1, ss2;
    ss1 << "__ESBMC_ptr_obj_start_" << id;
    symbol2tc ptr_start(int_type, ss1.str());
    ss2 << "__ESBMC_ptr_obj_end_" << id;
    symbol2tc ptr_end(int_type, ss2.str());

    obj_starts[i] = ptr_start;

    greaterthanequal2tc ge(target, ptr_start);
    lessthanequal2tc le(target, ptr_end);
    and2tc theand(ge, le);
    is_in_range[i] = theand;
  }

  // Generate a big ITE chain, selecing a particular pointer offset. A
  // significant question is what happens when it's neither; in which case I
  // suggest the ptr becomes invalid_object. However, this needs frontend
  // support to check for invalid_object after all dereferences XXXjmorse.

  // So, what's the default value going to be if it doesn't match any existing
  // pointers? Answer, it's going to be the invalid object identifier, but with
  // an offset that calculates to the integer address of this object.
  // That's so that we can store an invalid pointer in a pointer type, that
  // eventually can be converted back via some mechanism to a valid pointer.
  expr2tc id, offs;
  id = constant_int2tc(int_type, pointer_logic.back().get_invalid_object());

  // Calculate ptr offset - target minus start of invalid range, ie 1
  offs = sub2tc(int_type, target, one_uint);

  std::vector<expr2tc> membs;
  membs.push_back(id);
  membs.push_back(offs);
  constant_struct2tc prev_in_chain(pointer_struct, membs);

  // Now that big ite chain,
  for (i = 0; i < addr_space_data.back().size(); i++) {
    membs.clear();

    // Calculate ptr offset were it this
    offs = sub2tc(int_type, target, obj_starts[i]);

    membs.push_back(obj_ids[i]);
    membs.push_back(offs);
    constant_struct2tc selected_tuple(pointer_struct, membs);

    prev_in_chain = if2tc(pointer_struct, is_in_range[i],
                          selected_tuple, prev_in_chain);
  }

  // Finally, we're now at the point where prev_in_chain represents a pointer
  // object. Hurrah.
  return convert_ast(prev_in_chain);
}

const smt_ast *
smt_convt::convert_typecast_from_ptr(const typecast2t &cast)
{

  type2tc int_type(new unsignedbv_type2t(config.ansi_c.int_width));

  // The plan: index the object id -> address-space array and pick out the
  // start address, then add it to any additional pointer offset.

  pointer_object2tc obj_num(int_type, cast.from);

  symbol2tc addrspacesym(addr_space_arr_type, get_cur_addrspace_ident());
  index2tc idx(addr_space_type, addrspacesym, obj_num);

  // We've now grabbed the pointer struct, now get first element. Represent
  // as fetching the first element of the struct representation.
  member2tc memb(int_type, idx, addr_space_type_data->member_names[0]);

  pointer_offset2tc ptr_offs(int_type, cast.from);
  add2tc add(int_type, memb, ptr_offs);

  // Finally, replace typecast
  typecast2tc new_cast(cast.type, add);
  return convert_ast(new_cast);
}

const smt_ast *
convert_typecast_struct(const typecast2t &cast __attribute__((unused)))
{
  assert(0);
}

const smt_convt::expr_op_convert
smt_convt::smt_convert_table[expr2t::end_expr_id] =  {
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const int
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const fixedbv
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const bool
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const string
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const struct
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const union
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const array
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //const array_of
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //symbol
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //typecast
{ SMT_FUNC_ITE, SMT_FUNC_ITE, SMT_FUNC_ITE, 3, SMT_SORT_ALLINTS | SMT_SORT_BOOL},  //if
{ SMT_FUNC_EQ, SMT_FUNC_EQ, SMT_FUNC_EQ, 2, SMT_SORT_ALLINTS | SMT_SORT_BOOL},  //equality
{ SMT_FUNC_NOTEQ, SMT_FUNC_NOTEQ, SMT_FUNC_NOTEQ, 2, SMT_SORT_ALLINTS | SMT_SORT_BOOL},  //notequal
{ SMT_FUNC_LT, SMT_FUNC_BVSLT, SMT_FUNC_BVULT, 2, SMT_SORT_ALLINTS},  //lt
{ SMT_FUNC_GT, SMT_FUNC_BVSGT, SMT_FUNC_BVUGT, 2, SMT_SORT_ALLINTS},  //gt
{ SMT_FUNC_LTE, SMT_FUNC_BVSLTE, SMT_FUNC_BVULTE, 2, SMT_SORT_ALLINTS},  //lte
{ SMT_FUNC_GTE, SMT_FUNC_BVSGTE, SMT_FUNC_BVUGTE, 2, SMT_SORT_ALLINTS},  //gte
{ SMT_FUNC_NOT, SMT_FUNC_NOT, SMT_FUNC_NOT, 1, SMT_SORT_BOOL},  //not
{ SMT_FUNC_AND, SMT_FUNC_AND, SMT_FUNC_AND, 2, SMT_SORT_BOOL},  //and
{ SMT_FUNC_OR, SMT_FUNC_OR, SMT_FUNC_OR, 2, SMT_SORT_BOOL},  //or
{ SMT_FUNC_XOR, SMT_FUNC_XOR, SMT_FUNC_XOR, 2, SMT_SORT_BOOL},  //xor
{ SMT_FUNC_IMPLIES, SMT_FUNC_IMPLIES, SMT_FUNC_IMPLIES, 2, SMT_SORT_BOOL},//impl
{ SMT_FUNC_INVALID, SMT_FUNC_BVAND, SMT_FUNC_BVAND, 2, SMT_SORT_BV},  //bitand
{ SMT_FUNC_INVALID, SMT_FUNC_BVOR, SMT_FUNC_BVOR, 2, SMT_SORT_BV},  //bitor
{ SMT_FUNC_INVALID, SMT_FUNC_BVXOR, SMT_FUNC_BVXOR, 2, SMT_SORT_BV},  //bitxor
{ SMT_FUNC_INVALID, SMT_FUNC_BVNAND, SMT_FUNC_BVNAND, 2, SMT_SORT_BV},//bitnand
{ SMT_FUNC_INVALID, SMT_FUNC_BVNOR, SMT_FUNC_BVNOR, 2, SMT_SORT_BV},  //bitnor
{ SMT_FUNC_INVALID, SMT_FUNC_BVNXOR, SMT_FUNC_BVNXOR, 2, SMT_SORT_BV}, //bitnxor
{ SMT_FUNC_INVALID, SMT_FUNC_BVNOT, SMT_FUNC_BVNOT, 1, SMT_SORT_BV},  //bitnot
{ SMT_FUNC_INVALID, SMT_FUNC_BVLSHR, SMT_FUNC_BVLSHR, 2, SMT_SORT_BV},  //lshr
{ SMT_FUNC_NEG, SMT_FUNC_BVNEG, SMT_FUNC_BVNEG, 1, SMT_SORT_ALLINTS},  //neg
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //abs
{ SMT_FUNC_ADD, SMT_FUNC_BVADD, SMT_FUNC_BVADD, 2, SMT_SORT_ALLINTS},//add
{ SMT_FUNC_SUB, SMT_FUNC_BVSUB, SMT_FUNC_BVSUB, 2, SMT_SORT_ALLINTS},//sub
{ SMT_FUNC_MUL, SMT_FUNC_BVMUL, SMT_FUNC_BVMUL, 2, SMT_SORT_ALLINTS},//mul
{ SMT_FUNC_DIV, SMT_FUNC_BVDIV, SMT_FUNC_BVDIV, 2, SMT_SORT_ALLINTS},//div
{ SMT_FUNC_MOD, SMT_FUNC_BVSMOD, SMT_FUNC_BVUMOD, 2, SMT_SORT_BV | SMT_SORT_INT},//mod
{ SMT_FUNC_SHL, SMT_FUNC_BVSHL, SMT_FUNC_BVSHL, 2, SMT_SORT_BV | SMT_SORT_INT},  //shl

// Error: C frontend doesn't upcast the 2nd operand to ashr to the 1st operands
// bit width. Therefore this doesn't work. Fall back to backup method.
//{ SMT_FUNC_INVALID, SMT_FUNC_BVASHR, SMT_FUNC_BVASHR, 2, SMT_SORT_BV},  //ashr
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //ashr

{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //dyn_obj_id
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //same_obj_id
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //ptr_offs
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //ptr_obj
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //addr_of
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //byte_extract
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //byte_update
{ SMT_FUNC_STORE, SMT_FUNC_STORE, SMT_FUNC_STORE, 3, SMT_SORT_ARRAY | SMT_SORT_ALLINTS | SMT_SORT_BOOL},  //with
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //member
{ SMT_FUNC_SELECT, SMT_FUNC_SELECT, SMT_FUNC_SELECT, 2, SMT_SORT_ARRAY | SMT_SORT_INT | SMT_SORT_BV},  //index
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //zero_str_id
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //zero_len_str
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //isnan
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //overflow
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //overflow_cast
{ SMT_FUNC_HACKS, SMT_FUNC_HACKS, SMT_FUNC_HACKS, 0, 0},  //overflow_neg
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //unknown
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //invalid
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //null_obj
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //deref
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //valid_obj
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //deallocated
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //dyn_size
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //sideeffect
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_block
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_assign
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_init
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_decl
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_printf
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_expr
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_return
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_skip
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_free
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_goto
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //obj_desc
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_func_call
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_comma
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //invalid_ptr
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //buffer_sz
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //code_asm
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //cpp_del_arr
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //cpp_del_id
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //cpp_catch
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //cpp_throw
{ SMT_FUNC_INVALID, SMT_FUNC_INVALID, SMT_FUNC_INVALID, 0, 0},  //cpp_throw_dec
};
