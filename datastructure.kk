type literal
  BoolL(b: bool)
  IntL(i: int)
  CharL(c: char)
  FloatL(f: float64)

struct ident
  name: string

rec type expr
  ELit(v: literal)
  ETup(e0: list<expr>)
  EVar(ident: ident)
  App(e0: expr, e1: expr)
  Lam(ident: ident, e: expr)
  PrimOp(ident: ident, e: (evalue) -> exn evalue)
  Let(ident: ident, e0: expr, e1: expr);

rec type evalue
  Bool(bb: bool)
  Int(i: int)
  Char(c: char)
  Float(f: float64)
  Tuple(vals: list<evalue>)
  Clos(arg: ident, body: expr, env: list<(ident, evalue)>)
  PrimClos(body: (evalue) -> exn evalue);

alias environment = list<(ident, evalue)>

// Helper functions for stringifying datatypes
fun show(v: literal): string
  match v
    BoolL(b) -> b.show
    IntL(i) -> i.show
    CharL(c) -> c.show
    FloatL(f) -> f.show

fun show(t: ident): div string
  t.name

fun show(e: expr): div string
  match e
    ELit(value) -> "(Lit " ++ value.show ++ ")"
    ETup(es) -> "(" ++ es.foldl("", fn(acc, i) -> acc ++ i.show ++ ",") ++ ")" 
    EVar(ident) -> ident.show 
    App(e0, e1) -> "\n(" ++ e0.show ++ " " ++ e1.show ++ ")" 
    Lam(ident, e0) -> "\n(\\" ++ ident.name ++ "." ++ e0.show ++ ")"
    PrimOp(ident, _) -> "(Primitive " ++ ident.name ++ ")"
    Let(ident, e0, e1) -> "\n(let " ++ ident.show ++ " = " ++ e0.show ++ " in " ++ e1.show ++ ")"

fun show(v: evalue): div string
  match v
    Bool(b) -> b.show
    Int(i) -> i.show
    Char(c) -> c.show
    Float(f) -> f.show
    Tuple(vals) -> "(" ++ vals.foldl("", fn(acc, i) -> acc ++ i.show ++ ",") ++ ")"
    Clos(arg, body, env) -> "Clos(" ++ arg.name.show ++ ", " ++ body.show ++ ", " ++ env.show ++ ")"
    PrimClos(_) -> "Primitive Operation"

fun show(l: environment): div string
  if l.is-empty then "Environment: ()" else
    "Environment: (\n\t" ++ l.map(fn(x) x.fst.name ++ " = " ++ x.snd.show).join("\n\t") ++ ")\n"

fun show(x: (a,b), showA: (a) -> e string, showB: (b) -> e string): e string
  showA(x.fst) ++ "," ++ showB(x.snd)

fun eq(l1: list<a>, l2: list<a>, equal: (a, a) -> e bool): e bool
  match (l1, l2)
    ([], []) -> True
    (Cons(a,aas), Cons(b, bs)) -> equal(a, b) && aas.eq(bs,equal)
    _ -> False

fun (==)(i1: ident, i2: ident): div bool
  match (i1, i2)
    (Ident(a), Ident(b)) -> 
      a == b


