type literal
  BoolL(b: bool)
  IntL(i: int)
  CharL(c: char)
  FloatL(f: float64)

struct ident
  name: string

type expr
  ELit(v: literal)
  ETup(e0: list<expr>)
  EVar(ident: ident)
  App(e0: expr, e1: expr)
  Lam(ident: ident, e: expr)
  If(e0: expr, e1: expr, e2: expr)
  Let(ident: ident, e0: expr, e1: expr);

type evalue
  Bool(b: bool)
  Int(i: int)
  Char(c: char)
  Float(f: float64)
  Tuple(vals: list<evalue>)
  Clos(arg: ident, body: expr, env: list<(ident, int)>)
  PrimClos(name: ident); 

// Helper functions for stringifying datatypes
fun show(v: literal): string
  match v
    BoolL(b) -> b.show
    IntL(i) -> i.show
    CharL(c) -> c.show
    FloatL(f) -> f.show

fun show(t: ident): div string
  t.name

fun showLisp(e: expr): div string
  match e
    ELit(value) -> value.show
    ETup(es) -> es.foldl("", fn(acc, i) -> acc ++ i.showLisp ++ " ")
    EVar(ident) -> ident.show
    App(e0, e1) -> "( " ++ e0.showLisp ++ " " ++ e1.showLisp ++ ")"
    Lam(ident, e0) -> "(\\" ++ ident.name ++ " " ++ e0.showLisp ++ ")"
    Let(ident, e0, e1) -> "(let (" ++ ident.name ++ " " ++ e0.showLisp ++ ") " ++ e1.showLisp ++ ")"
    If(e0, e1, e2) -> "(if " ++ e0.showLisp ++ " " ++ e1.showLisp ++ " " ++ e2.showLisp ++ ")"

fun show(e: expr): div string
  match e
    ELit(value) -> "(Lit " ++ value.show ++ ")"
    ETup(es) -> "(" ++ es.foldl("", fn(acc, i) -> acc ++ i.show ++ ",") ++ ")" 
    EVar(ident) -> ident.show 
    App(e0, e1) -> "\n(" ++ e0.show ++ " " ++ e1.show ++ ")" 
    Lam(ident, e0) -> "\n(\\" ++ ident.name ++ "." ++ e0.show ++ ")"
    Let(ident, e0, e1) -> "\n(let " ++ ident.show ++ " = " ++ e0.show ++ " in " ++ e1.show ++ ")"
    If(e0, e1, e2) -> "\n(if " ++ e0.show ++ " then " ++ e1.show ++ " else " ++ e2.show ++ ")"

fun show(v: evalue): div string
  match v
    Bool(b) -> b.show
    Int(i) -> i.show
    Char(c) -> c.show
    Float(f) -> f.show
    Tuple(vals) -> "(" ++ vals.foldl("", fn(acc, i) -> acc ++ i.show ++ ",") ++ ")"
    Clos(arg, body, env) -> "Clos(" ++ arg.name.show ++ ", " ++ body.show ++ ", " ++ env.show ++ ")"
    PrimClos(_) -> "Primitive Operation"

fun show(v: maybe<evalue>): div string
  match v
    Just(vv) -> vv.show
    Nothing -> "Nothing"

fun show(l: list<(ident,int)>): div string
  if l.is-empty then "Environment: ()" else
    "Environment: (\n\t" ++ l.map(fn(x) x.fst.name ++ " = " ++ x.snd.show).join("\n\t") ++ ")\n"

fun show(l: vector<maybe<evalue>>): div string
  match l.at(0)
    Just(Nothing) -> "Store: ()"
    _ ->
      var ind := 0
      var out := "Store: (\n\t"
      l.foreach-while fn(x)
        if ind >= (l.length - 1) then
          Just(False)
        else 
          match x
            Just(v) -> 
              out := out ++ ind.show ++ " = " ++ v.show ++ "\n\t"
              ind := ind + 1
              Nothing
            Nothing -> Just(False)
          Nothing
      out := out ++ "\n)\n"
      out

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

fun (==)(l0: literal, l1: literal): bool
  match (l0, l1)
    (BoolL(b0), BoolL(b1)) -> b0 == b1
    (IntL(i0), IntL(i1)) -> i0 == i1
    (CharL(c0), CharL(c1)) -> c0 == c1
    (FloatL(f0), FloatL(f1)) -> f0 == f1
    (_, _) -> False

fun (==)(e0: expr, e1: expr): div bool
  match (e0, e1)
    (ELit(l0), ELit(l1)) -> l0 == l1
    (ETup(es0), ETup(es1)) -> es0.eq(es1, fn(a,b) a == b)
    (EVar(i0), EVar(i1)) -> i0 == i1
    (App(e00, e01), App(e10, e11)) -> e00 == e10 && e01 == e11
    (Lam(i0, e00), Lam(i1, e10)) -> i0 == i1 && e00 == e10
    (If(e00, e01, e02), If(e10, e11, e12)) -> e00 == e10 && e01 == e11 && e02 == e12
    (Let(i0, e00, e01), Let(i1, e10, e11)) -> i0 == i1 && e00 == e10 && e01 == e11
    _ -> False


