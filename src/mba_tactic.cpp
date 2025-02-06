#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/bv/mba_tactic.h"
// {{{
#include "ast/ast_pp.h"
// }}}
#include "ast/bv_decl_plugin.h"

#include <tuple>
#include <vector>

// {{{
#define MARKER
// }}}

namespace {

const size_t kBVSize = 64;

int basis[][4] = {
  {0, 0, 0, 0},
  {-1, -1, 1, 1},
  {0, 1, -1, 0},
  {-1, 0, 0, 1},
  {1, 0, -1, 0},
  {0, -1, 0, 1},
  {1, 1, -2, 0},
  {0, 0, -1, 1},
  {0, 0, 1, 0},
  {-1, -1, 2, 1},
  {0, 1, 0, 0},
  {-1, 0, 1, 1},
  {1, 0, 0, 0},
  {0, -1, 1, 1},
  {1, 1, -1, 0},
  {0, 0, 0, 1}
};

struct bool_function {
  using boolvar = std::tuple<bool, char>;
  expr_ref e;
  char op;
  std::vector<boolvar> vars;
  bool negated;

  bool_function(ast_manager & m, expr * e) : e(e, m), op(0), negated(false) { }

  bool evaluate(bool x, bool y) {
    auto eval_var = [&](const boolvar & v) {
      bool neg; char name;
      std::tie(neg, name) = v;
      return neg ? !((name == 'x' ? x : y)) : (name == 'x' ? x : y);
    };

    bool result;
    switch (op) {
    case '&': result = eval_var(vars[0]) && eval_var(vars[1]); break;
    case '|': result = eval_var(vars[0]) || eval_var(vars[1]); break;
    case '^': result = eval_var(vars[0]) ^ eval_var(vars[1]); break;
    default: result = eval_var(vars[0]); break;
    }
    return negated ? !result : result;
  }

  int truth_value(void) {
    int result = 0;
    for (size_t i = 0; i < 4; i++) {
      bool x = i & 2;
      bool y = i & 1;
      if (evaluate(x, y))
        result |= 1 << i;
    }
    return result;
  }
// {{{
#ifdef MARKER
  friend std::ostream & operator<<(std::ostream & os, const bool_function & bf) {
    if (bf.negated) 
      os << "~";

    if (bf.vars.size() > 1)
      os << "(";
    for (size_t i = 0; i < bf.vars.size(); i++) {
      bool neg; char name;
      std::tie(neg, name) = bf.vars[i];
      os << (neg ? "~" : "") << name;
      if (i < bf.vars.size() - 1)
        os << bf.op;
    }

    if (bf.vars.size() > 1)
      os << ")";
    return os;
  }
#endif
// }}}
};


using coeff_type = long long;
using mba_term = std::tuple<coeff_type, bool_function>;


struct mba_expr {
  std::vector<mba_term> terms;
  ast_manager & m;

  mba_expr(ast_manager & m) : m(m) { }
// {{{
#ifdef MARKER
  friend std::ostream& operator<<(std::ostream & os, const mba_expr & mba) {
    for (size_t i = 0; i < mba.terms.size(); i++) {
      const mba_term & term = mba.terms[i];
      os << std::get<0>(term) << "*" << std::get<1>(term);
      if (i < mba.terms.size() - 1)
        os << " + ";
    }
    return os; 
  }
#endif
// }}}
};

class mba_tactic : public tactic {
  ast_manager & m_manager;
  bv_util m_bv_util;
  params_ref m_params;

  ast_manager & m() const { return m_manager; }

  bv_util & bv() { return m_bv_util; }

  coeff_type get_coeff(expr * e) {
    rational r;
    if (!bv().is_numeral(e, r))
      throw tactic_exception("expected numeral");
    
    if (r.is_int64())
      return r.get_int64();
    else if (r.is_int32())
      return r.get_int32();
    else if (r.is_uint64()) {
      return r.get_uint64();
    }
    throw tactic_exception("expected int64");
  }

  bool is_indeterminate(expr * e) {
    if (!is_app(e))
      return false;

    app * a = to_app(e);
    if (a->get_num_args() != 0)
      return false;

    sort * s = a->get_decl()->get_range();
    if (!bv().is_bv_sort(s))
      return false;

    unsigned bv_size = s->get_parameter(0).get_int();
    if (bv_size != kBVSize)
      return false;

    func_decl * f = a->get_decl();
    if (f->get_name() == "x" || f->get_name() == "y")
      return true;
    return false;
  }

  expr * mk_indeterminate(const char* name) {
    return m().mk_const(name, bv().mk_sort(kBVSize));
  }

  expr * mk_numeral(int64_t u) {
    return bv().mk_numeral(u, kBVSize);
  }

  bool build_bool_function_terms(app * a, bool_function & bf) {
    unsigned num_args = a->get_num_args();
    if (num_args > 2) {
// {{{
#ifdef MARKER
      TRACE("mba", tout << "too many args\n";);
#endif
// }}}
      return false;
    }

    for (unsigned i = 0; i < num_args; i++) {
      expr * arg = a->get_arg(i);
      if (!is_app(arg)) {
// {{{
#ifdef MARKER
        TRACE("mba", tout << "not an app\n";);
#endif
// }}} 
        return false;
      }
      app * arg_app = to_app(arg);

      if (bv().is_bv_not(arg_app)) {
        expr * indet = arg_app->get_arg(0);
        if (!is_indeterminate(indet)) {
// {{{
#ifdef MARKER 
          TRACE("mba", tout << "not an indeterminate\n";);
#endif
// }}} 
          return false;
        }
        char name = to_app(indet)->get_decl()->get_name().str()[0];
        bf.vars.push_back(std::make_tuple(true, name));
      } else if (is_indeterminate(arg_app)) {
        char name = arg_app->get_decl()->get_name().str()[0];
        bf.vars.push_back(std::make_tuple(false, name));
      } else {
        TRACE("mba", tout << "not an indeterminate\n";);
        return false;
      }
    }
    return true;
  }

  bool build_bool_function(expr * e, bool_function & bf) {
    if (!is_app(e))
      return false;
// {{{
#ifdef MARKER
    TRACE("mba", tout << "build_bool_function " << mk_pp(e, m()) << "\n";);
#endif
// }}}

    app * a = to_app(e);
    if (bv().is_bv_not(a)) {
      bf.negated = !bf.negated;
      return build_bool_function(a->get_arg(0), bf);
    } else if (bv().is_bv_and(a)) {
      bf.op = '&';
      return build_bool_function_terms(a, bf);
    } else if (bv().is_bv_or(a)) {
      bf.op = '|';
      return build_bool_function_terms(a, bf);
    } else if (bv().is_bv_xor(a)) {
      bf.op = '^';
      return build_bool_function_terms(a, bf);
    }

    if (!is_indeterminate(a))
      return false;

    char name = a->get_decl()->get_name().str()[0];
    bf.vars.push_back(std::make_tuple(false, name));
    return true;
  }

  bool build_mba_expr(expr * e, mba_expr & mba, bool negative) {
    if (!is_app(e))
      return false;
// {{{
#ifdef MARKER
    TRACE("mba", tout << "build_mba_expr " << mk_pp(e, m()) << "\n";);
#endif
// }}}

    app * a = to_app(e);
    if (bv().is_bv_add(a)) {
      unsigned num_args = a->get_num_args();
// {{{
#ifdef MARKER 
      TRACE("mba", tout << "bv_add " << num_args << "\n";);
#endif
// }}}
      
      if (num_args != 2)
        return false;

      expr * arg1 = a->get_arg(0);
      expr * arg2 = a->get_arg(1);

      if (!build_mba_expr(arg1, mba, negative))
        return false;
      if (!build_mba_expr(arg2, mba, negative))
        return false;
      return true;
    } else if (bv().is_bv_sub(a)) {
// {{{
#ifdef MARKER 
      TRACE("mba", tout << "bv_sub\n";);
#endif
// }}}
      unsigned num_args = a->get_num_args();
      if (num_args != 2)
        return false;

      expr * arg1 = a->get_arg(0);
      expr * arg2 = a->get_arg(1);

      if (!build_mba_expr(arg1, mba, negative))
        return false;
      if (!build_mba_expr(arg2, mba, !negative))
        return false;
      return true;
    } else if (bv().is_bv_mul(a)) {
// {{{
#ifdef MARKER
      TRACE("mba", tout << "bv_mul\n";);
#endif
// }}} 
      if (a->get_num_args() != 2)
        return false;

      expr * coef = a->get_arg(0);
      expr * term = a->get_arg(1);
      if (!bv().is_numeral(coef))
        return false;

      bool_function bf(m(), term);
      if (!build_bool_function(term, bf))
        return false;

      coeff_type c = get_coeff(coef);
      if (negative)
        c = -c;
      mba.terms.push_back(std::make_tuple(c, bf));
      return true;
    } else if (bv().is_numeral(a)) {
// {{{
#ifdef MARKER 
      TRACE("mba", tout << "bv_numeral\n";);
#endif
// }}} 
      expr * indet = mk_indeterminate("x");
      expr * term = bv().mk_bv_not(bv().mk_bv_and(indet,bv().mk_bv_not(indet)));

      bool_function bf(m(), term);
      if (!build_bool_function(term, bf))
        return false;

      coeff_type c = get_coeff(a);
      if (negative)
        c = -c;
      mba.terms.push_back(std::make_tuple(-c, bf));
      return true;
    }

    // probably a bool function
// {{{
#ifdef MARKER 
    TRACE("mba", tout << "bool_function " << a->get_decl()->get_name() << '\n';);
#endif
// }}}
    bool_function bf(m(), e);
    if (!build_bool_function(e, bf))
      return false;

    coeff_type c = negative ? -1 : 1;
    mba.terms.push_back(std::make_tuple(c, bf));
    return true;
  }

  expr * mk_expressiion(int * basis) {
    expr * x = mk_indeterminate("x");
    expr * y = mk_indeterminate("y");
    expr * x_and_y = bv().mk_bv_and(x, y);
    expr * one = mk_numeral(-1ull);
    expr * basis_expr[] = { x, y, x_and_y, one };

    expr * result = nullptr;
    for (size_t i = 0; i < 4; i++) {
      if (basis[i] == 0)
        continue;

      expr * coterm = bv().mk_bv_mul(
        mk_numeral(basis[i]),
        basis_expr[i]
      );
      if (!result)
        result = coterm;
      else
        result = bv().mk_bv_add(result, coterm);
    }
    return result;
  }

  expr * construct_simplified_mba(expr * e) {
    mba_expr mba(m());

    if (!build_mba_expr(e, mba, false))
      return nullptr;

// {{{
#ifdef MARKER
    TRACE("mba", tout << "mba: " << mba << "\n";);
#endif
// }}}
    int basis_comb[4] = {0, 0, 0, 0};
    for (size_t i = 0; i < mba.terms.size(); i++) {
      int truth_value = std::get<1>(mba.terms[i]).truth_value();
      coeff_type coeff = std::get<0>(mba.terms[i]);
      for (size_t j = 0; j < 4; j++) {
        basis_comb[j] += basis[truth_value][j] * coeff;
      }
// {{{
#ifdef MARKER
      TRACE("mba", 
        tout << "truth_value: " << truth_value << "\n";
        tout << "coeff: " << coeff << "\n";
        tout << "basis_comb: ";
        for (size_t i = 0; i < 4; i++) {
          tout << basis_comb[i] << " ";
        }
        tout << "\n";
      );
#endif
// }}}
    }
// {{{
#ifdef MARKER
    TRACE("mba", 
      tout << "basis_comb: ";
      for (size_t i = 0; i < 4; i++) {
        tout << basis_comb[i] << " ";
      }
      tout << "\n";
    );
#endif
// }}}
    return mk_expressiion(basis_comb);
  }

  bool simplify_form(expr * e, expr_ref & result) {
    if (!is_app(e))
      return false;

    app * a = to_app(e);
    
    if (m().is_eq(a) || m().is_distinct(a)) {
      SASSERT(a->get_num_args() == 2);
      expr * lhs = a->get_arg(0);
      expr * rhs = a->get_arg(1);
      expr * simplified = construct_simplified_mba(lhs);
      
      if (simplified) {
        if (m().is_eq(a))
          result = m().mk_eq(simplified, rhs);
        else {
          expr * args[] = { simplified, rhs };
          result = m().mk_distinct(2, args);
        }
        return true;
      }
    }
    return false;
  }

  void simplify_goal(goal & g) {
    if (g.inconsistent())
      return;
    if (g.proofs_enabled()) {
// {{{
#ifdef MARKER
      TRACE("mba", tout << "mba tactic does not support proofs\n";);
#endif
// }}}
      return; // not supported
    }

    expr_ref new_curr(m());
    proof_ref new_pr(m());
    unsigned size = g.size();
    for(unsigned idx = 0; idx < size; idx++) {
      if (g.inconsistent()) {
        break;
      }
      expr * curr = g.form(idx);
// {{{
#ifdef MARKER
      TRACE("mba", 
        tout << "before: " << mk_pp(curr, m()) << "\n";
        tout << "is_app: " << is_app(curr) << "\n";
      );
#endif
// }}} 
      if (simplify_form(curr, new_curr)) {
        g.update(idx, new_curr, new_pr, g.dep(idx));
      }
    }
  }

public:
  mba_tactic(ast_manager & m, params_ref const & p) : m_manager(m), m_bv_util(m), m_params(p) { }

  void collect_statistics(statistics & st) const override { }

  void operator()(goal_ref const & in, goal_ref_buffer & result) override {
    TRACE("mba", tout << "mba tactic\n";);
    simplify_goal(*in.get());
    in->inc_depth();
    result.push_back(in.get());
  }
  
  void cleanup() override { }

  tactic * translate(ast_manager & m) override { return alloc(mba_tactic, m, m_params); }

  const char* name() const override { return "mba"; }
};

} // namespace

tactic * mk_mba_tactic(ast_manager & m, params_ref const & p) {
  return clean(alloc(mba_tactic, m, p));
}
