from lark import Lark, Transformer
from typing import Any, List, Tuple, Self
import numpy as np
import sympy as sp
import z3

BITSET = {
  'x': [0, 0, 1, 1],
  'y': [0, 1, 0, 1],
}
TRUTH_BASIS = ["x", "y", "(x&y)", "~(x&~x)"]

# Every boolean function can be transformed into one of these.
BIT_BASIS = [
  '(x&~x)', '~(x|y)', '~(x|~y)', '~x', 
  '(x&~y)', '~y', '(x^y)', '~(x&y)',
  '(x&y)', '~(x^y)', 'y', '~(x&~y)',
  'x', '(x|~y)', '(x|y)', '~(x&~x)',
]

Rule = r"""
?start: expr -> expression

?expr: coterm -> coefterm
    | expr "+" coterm -> add
    | expr "-" coterm -> sub

?coterm: term -> term
    | NUMBER "*" term -> mul             
    | NUMBER -> const
              
?term: "(" term ")"
    | "~" "(" term ")" -> bnot_term
    | factor "&" factor -> band
    | factor "|" factor -> bor
    | factor "^" factor -> bxor
    | factor -> single
              
?factor: "x" -> x
    | "y" -> y
    | "~" factor -> bnot

%import common.NUMBER
%import common.WS
%ignore WS           
"""

P = Lark(Rule, parser='lalr', start='start')
PT = Lark(Rule, parser='lalr', start='term')

class MBATransformer(Transformer):
  def expression(self, args):
    return MBAExpr(args[0])

  def coefterm(self, args):
    return [args[0]]

  def add(self, args):
    return args[0] + [args[1]]

  def sub(self, args):
    new_arg = (-args[1][0], args[1][1])
    return args[0] + [new_arg]

  def term(self, args):
    return (1, args[0])

  def mul(self, args):
    num = int(args[0])
    return (num, args[1])

  def const(self, args):
    num = int(args[0])
    return (num, BoolFunction('&', ['x', '~x'], True))
  
  def bnot_term(self, args):
    return args[0].invert()

  def band(self, args):
    return BoolFunction('&', args)

  def bor(self, args):
    return BoolFunction('|', args)

  def bxor(self, args):
    return BoolFunction('^', args)
  
  def single(self, args):
    return BoolFunction(None, args)

  def x(self, args):
    return 'x'

  def y(self, args):
    return 'y'

  def bnot(self, args):
    if args[0] == 'x' or args[0] == 'y':
      return '~' + args[0]
    assert args[0][0] == '~', "Invalid expression"
    return args[0][1]   # double negation

boolean = lambda x: 1 if x else 0
def _handle_bop(op: str, a: List[int] | int, b: List[int] | int) -> List[int] | int:
  if op == '&':
    if isinstance(a, int):
      return boolean(a) & boolean(b)
    return [boolean(x) & boolean(y) for x, y in zip(a, b)]
  elif op == '|':
    if isinstance(a, int):
      return boolean(a) | boolean(b)
    return [boolean(x) | boolean(y) for x, y in zip(a, b)]
  elif op == '^':
    if isinstance(a, int):
      return boolean(a) ^ boolean(b)
    return [boolean(x) ^ boolean(y) for x, y in zip(a, b)]
  raise ValueError("Invalid binary operator")

def _handle_uop(op: str, a: List[int] | int) -> List[int] | int:
  if op != '~':
    raise ValueError("Invalid unary operator")
  if isinstance(a, int):
    return boolean(1 if a == 0 else 0)
  return [boolean(1 if x == 0 else 0) for x in a]

def _get_bitvec(s: str, nbits: int) -> z3.BitVec:
  return z3.BitVec(s, nbits)

def _get_bitvecval(v: int, nbits: int) -> z3.BitVecVal:
  return z3.BitVecVal(v, nbits)

class BoolFunction(object):
  def __init__(self, op: str | None, args: List[str], inverted: bool = False):
    if op is not None:
      assert len(args) == 2, "Binary operator must have two arguments"
    else:
      assert len(args) == 1, "A bool function must have at least one argument"
      if inverted and args[0] == '~':   # double neg
        inverted = False
        args = [args[0][1]]
    self.op = op
    self.args = args
    self.inverted = inverted

  def __str__(self):
    if self.op is not None:
      s = "(" + self.op.join(self.args) + ")"
    else:
      s = self.args[0]  
    
    if self.inverted:
      return f"~{s}"
    return s
  
  def __repr__(self):
    return str(self)
  
  def _get_arg_symbol(self, s: str) -> str:
    if s[0] != '~':
      return s
    return s[1]
  
  def _get_bitset(self, s: str) -> List[int]:
    if s[0] != '~':
      return BITSET[s]
    return _handle_uop('~', self._get_bitset(s[1]))
  
  def _eval_arg(self, s: str, x: int, y: int) -> int:
    bitset = {'x': x, 'y': y}
    if s[0] != '~':
      return bitset[s]
    return _handle_uop('~', bitset[s[1]])
  
  def truth_table(self) -> List[int]:
    if self.op is not None:
      r = _handle_bop(self.op, self._get_bitset(self.args[0]), self._get_bitset(self.args[1]))
      if self.inverted:
        return _handle_uop('~', r)
      return r
    return self._get_bitset(self.args[0])
  
  def evaluate(self, x: int, y: int) -> int:
    if self.op is not None:
      r = _handle_bop(self.op, self._eval_arg(self.args[0], x, y), self._eval_arg(self.args[1], x, y))
      if self.inverted:
        return _handle_uop('~', r)
      return r
    return self._eval_arg(self.args[0], x, y)
  
  def invert(self) -> Self:
    return BoolFunction(self.op, self.args, not self.inverted)
  
  def _get_arg_z3expr(self, s: str, nbits: int) -> z3.BitVecRef:
    if s[0] != '~':
      return _get_bitvec(s, nbits)
    return ~(_get_bitvec(s[1], nbits))
  
  def to_z3expr(self, nbits: int) -> Any:
    if not self.op:
      arg_expr = self._get_arg_z3expr(self.args[0], nbits)
      if self.inverted:
        return ~arg_expr
      return arg_expr
    
    a = self._get_arg_z3expr(self.args[0], nbits)
    b = self._get_arg_z3expr(self.args[1], nbits)
    if self.op == '&':
      expr = a & b
    elif self.op == '|':
      expr = a | b
    elif self.op == '^':
      expr = a ^ b
    else:
      raise ValueError("Invalid operator")

    if self.inverted:
      return ~expr
    return expr
    


class MBAExpr(object):
  def __init__(self, coterms: List[Tuple[int, BoolFunction]]):
    self._coterms = coterms

  def __len__(self):
    return len(self._coterms)
  
  def __getitem__(self, i: int) -> Tuple[int, BoolFunction]:
    return self._coterms[i]
  
  def __setitem__(self, i: int, v: Tuple[int, BoolFunction] | BoolFunction):
    coef = self._coterms[i][0]
    if isinstance(v, BoolFunction):
      self._coterms[i] = (coef, v)
    else:
      self._coterms[i] = v

  def __str__(self):
    r = ""
    for c, t in self._coterms:
      if c < 0:
        r += f"-{abs(c)}*{t}"
      else:
        r += f"+{c}*{t}"
    return r
  
  def __repr__(self):
    return str(self)
  
  def to_z3expr(self, nbits: int) -> z3.BitVecRef:
    expr = 0
    for c, t in self._coterms:
      expr += _get_bitvecval(c, nbits) * t.to_z3expr(nbits)
    return expr
  
  def simplify(self) -> Self:
    raise NotImplementedError

class MBASimplifier(object):
  def __init__(self, basis: List[str]):
    self._basis = [parse_term(b) for b in basis]
    assert len(basis) == 4, "Basis must have 4 elements"
    self._truth_basis = [b.truth_table() for b in self._basis]
    self._symvars = [sp.symbols(f'X{i}') for i in range(4)]
    self._symvar_map = {self._symvars[i]: self._basis[i] for i in range(4)}
    self._build_bit_basis()
    
  def _build_bit_basis(self):
    self._bit_basis_expr = [parse_term(b) for b in BIT_BASIS]
    bit_truth_list = []
    A = np.asmatrix(self._truth_basis).T
    for bf in self._bit_basis_expr:
      basis_truth_table = bf.truth_table()
      b = np.asmatrix(basis_truth_table).T
      # represent the basis function in terms of the truth basis
      s = np.linalg.solve(A, b)
      r = np.array(s).reshape(-1,).tolist()
      r = [int(x) for x in r]
      bit_truth_list.append(r)
    self._bit_truth_list = bit_truth_list

  def _sym_expr_to_mba(self, sym_expr: Any) -> MBAExpr:
    coterm = []
    for symvar in self._symvars:
      sym_coef = sym_expr.coeff(symvar)
      if sym_coef.free_symbols:
        raise ValueError("Expression too complex to convert to MBAExpr")
      
      coef = int(sym_coef)
      if coef != 0:
        term = self._symvar_map[symvar]
        coterm.append((coef, term))
    return MBAExpr(coterm)

  def simplify(self, expr: MBAExpr) -> MBAExpr:
    sym_expr = 0
    for i in range(len(expr)):
      coef, term = expr[i]
      truth = term.truth_table()

      index = 0
      for i, v in enumerate(truth):
        index += v * (1 << i)

      basis_vec = self._bit_truth_list[index]
      sub_sym_expr = 0      
      for i, v in enumerate(basis_vec):
        sub_sym_expr += v * self._symvars[i]
      sym_expr += coef * sub_sym_expr
    
    sym_expr = sp.simplify(sym_expr)
    return self._sym_expr_to_mba(sym_expr)
    
T = MBATransformer()
def parse(expr: str) -> MBAExpr:
  return T.transform(P.parse(expr))

def parse_term(term: str) -> BoolFunction:
  return T.transform(PT.parse(term))

if __name__ == '__main__':
  print(parse("x-y"))
  print(parse('~(x|~y)'))
  basis_table = [parse_term(b) for b in BIT_BASIS]
  for b in basis_table:
    print(b, b.truth_table(), b.evaluate(1, 1))

  mba = parse('2*y+2*(x&~y)-(x^y)')
  print(mba)
  s = MBASimplifier(TRUTH_BASIS)
  print(s.simplify(mba))