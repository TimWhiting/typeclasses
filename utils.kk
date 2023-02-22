import datastructure

// Helper functions for creating expressions
fun eInt(i: int): expr
  ELit(IntL(i))

fun eChar(c: char): expr
  ELit(CharL(c))

fun eBool(c: bool): expr
  ELit(BoolL(c))

fun eFloat(c: float64): expr
  ELit(FloatL(c))

fun ident(name: string): ident
  Ident(name)

fun eVar(name: string): expr
  EVar(Ident(name))

fun contains(l: list<a>, a: a, equal: (a,a) -> e bool): e bool
  l.foldl(False, fn(acc, x) x.equal(a) || acc)


fun upsert(e: list<(ident, int)>, x: ident, a: int): list<(ident, int)>
  val removed = e.filter(fn (xi) unsafe-total(fn() !(xi.fst == x)))
  Cons((x, a), removed)

fun getAddr(e: list<(ident, int)>, x: ident): exn maybe<int>
  e.find(fn(xi) unsafe-total(fn() xi.fst == x)).map(fn(xi) xi.snd)

fun subexps(e: expr): div list<expr>
  val x = match e
    EVar(_) -> []
    ELit(_) -> []
    ETup(es) -> es.foldl([], fn(acc, ex) -> acc.set-union(ex.subexps, (==)))
    Lam(_, e0) -> subexps(e0)
    App(e1, e2) -> subexps(e1).set-union(subexps(e2),(==))
    Let(_, e1, e2) -> subexps(e1).set-union(subexps(e2),(==))
    If(e1, e2, e3) -> subexps(e1).set-union(subexps(e2),(==)).set-union(subexps(e3),(==))
    PrimOp(_) -> []
  x.set-add(e, (==))

fun set-add(l: list<x>, e: x, eq: (x, x) -> e bool): e list<x>
  if l.contains(e, eq) then l else Cons(e, l)

fun set-union(l: list<x>, l2: list<x>, eq: (x, x) -> e bool): e list<x>
  l2.foldl(l, fn(acc, e) acc.set-add(e, eq))

fun set-remove(l: list<x>, e: x, eq: (x, x) -> e bool): e list<x>
  l.filter(fn(e0) !eq(e0, e))