/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>

#include <hash_cont.h>
#include <options.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/boolector/boolector_dec.h>
#include <solvers/z3/z3_dec.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/sat/cnf_clause_list.h>
#include <langapi/language_ui.h>
#include <goto-symex/symex_target_equation.h>

#include "symex_bmc.h"

class bmc_baset:public messaget
{
public:
  bmc_baset(
    const contextt &_context,
    symex_bmct &_symex,
    symex_target_equationt &_equation,
    message_handlert &_message_handler):
    messaget(_message_handler),
    context(_context),
    symex(_symex),
    equation(&_equation),
    //equation(_equation),
    ui(ui_message_handlert::PLAIN)
  {
    _unsat_core=0;
  }

  uint _unsat_core;
  uint _number_of_assumptions;
  optionst options;

  virtual bool run(const goto_functionst &goto_functions);
  virtual ~bmc_baset() { }

  // additional stuff
  expr_listt bmc_constraints;

  friend class cbmc_satt;
  friend class hw_cbmc_satt;
  friend class counterexample_beautification_greedyt;

  void set_ui(language_uit::uit _ui) { ui=_ui; }

protected:
  const contextt &context;
  symex_bmct &symex;
  symex_target_equationt *equation;
  //symex_target_equationt &equation;

  // use gui format
  language_uit::uit ui;

#ifdef BOOLECTOR
  virtual bool decide_solver_boolector();
  virtual bool boolector();
  virtual bool boolector_conv(std::ostream &out);
#endif
  virtual bool decide_solver_z3();
  virtual bool z3();
  virtual bool z3_conv(std::ostream &out);

  virtual bool decide_default();
  virtual bool bv_refinement();
  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);
  virtual bool cvc();
  virtual bool cvc_conv(std::ostream &out);
  virtual bool smt();
  virtual bool smt_conv(std::ostream &out);
  virtual bool write_dimacs();
  virtual bool write_dimacs(std::ostream &out);

  // unwinding
  virtual void setup_unwind();

  virtual void do_unwind_module(
    decision_proceduret &decision_procedure);

  virtual void do_cbmc(prop_convt &solver);
  virtual void show_vcc();
  virtual void show_vcc(std::ostream &out);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace(
    const prop_convt &prop_conv);
    bool run_thread(const goto_functionst &goto_functions);
};

class bmct:public bmc_baset
{
public:
  bmct(
    const contextt &_context,
    message_handlert &_message_handler):
    bmc_baset(_context, _symex, _equation, _message_handler),
    ns(_context, new_context),
    _equation(ns),
    _symex(ns, new_context, _equation)
  {
  }

protected:
  contextt new_context;
  namespacet ns;
  symex_target_equationt _equation;
  symex_bmct _symex;
};

#endif
