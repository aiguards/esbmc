/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_H
#define CPROVER_PROP_H

// decision procedure wrapper for boolean propositional logics

#include <vector>

#include <message.h>
#include <threeval.h>

#include "literal.h"

class propt:public virtual messaget
{
public:
  propt() { }
  virtual ~propt() { }

  // boolean operators
  virtual literalt land(literalt a, literalt b)=0;
  virtual literalt lor(literalt a, literalt b)=0;
  virtual literalt land(const bvt &bv)=0;
  virtual literalt lor(const bvt &bv)=0;
  virtual literalt lnot(literalt a)=0;
  virtual literalt limplies(literalt a, literalt b)=0;
  virtual void set_equal(literalt a, literalt b);

  virtual void l_set_to(literalt a, bool value)
  {
    set_equal(a, const_literal(value));
  }

  void l_set_to_true(literalt a)
  { l_set_to(a, true); }
  void l_set_to_false(literalt a)
  { l_set_to(a, false); }

  // constraints
  virtual void lcnf(const bvt &bv)=0;

  // variables
  virtual literalt new_variable()=0;
  virtual unsigned no_variables() const=0;

  // solving
  virtual const std::string solver_text()=0;
  typedef enum { P_SATISFIABLE, P_UNSATISFIABLE, P_ERROR, P_SMTLIB } resultt;

  // satisfying assignment
  virtual tvt l_get(literalt a) const=0;
};

#endif
