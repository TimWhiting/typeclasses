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

fun getBool(b: evalue): exn bool
  match b
    Bool(bl) -> bl
    _ -> throw("Not a bool")

fun upsert(e: list<(ident, int)>, x: ident, a: int): list<(ident, int)>
  val removed = e.filter(fn (xi) unsafe-total(fn() !(xi.fst == x)))
  Cons((x, a), removed)

fun getAddr(e: list<(ident, int)>, x: ident): exn maybe<int>
  e.find(fn(xi) unsafe-total(fn() xi.fst == x)).map(fn(xi) xi.snd)