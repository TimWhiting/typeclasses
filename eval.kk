import datastructure
import utils
import primitives

alias primop<v> = (v) -> exn v

effect store<a,v>
  fun alloc(x: ident): a // Address
  fun extendStore(x: a, v: v): () // Extend store
  fun find(i: a): v // Value
  fun askStore(): vector<maybe<v>> // Store

effect env<a, v>
  fun askEnv(): list<(ident,a)> // Environment
  fun pushEnv(e: list<(ident, a)>, x: ident, a: a): ()
  fun popEnv(): ()

effect exprInfo
  fun doSomething(e: expr): ()

effect abst<a,v>
  ctl zero(v: v): bool
  fun primOp(x: ident): primop<v>
  fun intV(v: int): v
  fun floatV(v: float64): v
  fun charV(v: char): v
  fun boolV(v: bool): v
  fun tupleV(v: list<v>): v
  fun primClos(i: ident): v
  fun closV(x: ident, e: expr, cenv: list<(ident, a)>): v
  fun getClosure(v: v): evalue

alias interp<a,v> = <store<a,v>, env<a,v>, abst<a,v>, exprInfo, pure>

fun eval(x: expr): <interp<int,v>> v
  doSomething(x)
  // (x.show() ++ " where bindings " ++ env.show()).trace()
  match x
    // Literals
    ELit(IntL(v)) -> intV(v)
    ELit(FloatL(v)) -> floatV(v)
    ELit(CharL(v)) -> charV(v)
    ELit(BoolL(v)) -> boolV(v)
    ETup(v) -> tupleV(v.map(fn (vi) eval(vi)))
    // Primitive operations
    PrimOp(i) -> primClos(i)
    EVar(x1) -> 
      val e = askEnv()
      match e.getAddr(x1)
        Just(a) -> find(a)
        Nothing ->
          match lookupPrim(x1)
            Just(PrimOp(i)) -> primClos(i)
            Nothing -> throw("Unbound variable " ++ x.show ++ " in environment " ++ e.show)
    If(e0, e1, e2) ->
      val res = eval(e0)
      if !zero(res) then eval(e1) else eval(e2)
    Lam(x1, e1) -> closV(x1, e1, askEnv())
    // Let(i, e0, e1) ->
    //   rho' = Cons((i, ev(e0)))
    //   ev(e1)
    App(e0, e1) -> 
      val f = eval(e0).getClosure
      match f
        Clos(arg, body, cenv) -> 
          val v1 = eval(e1)
          val a = alloc(arg)
          extendStore(a, v1)
          pushEnv(cenv, arg, a)
          val v = eval(body)
          popEnv()
          v
        PrimClos(f1) -> 
          primOp(f1)(eval(e1))
        _ -> throw("Non-function value in function position " ++ e1.show)
    _ -> throw("Not implemented yet " ++ x.show)

fun basicEnv(f)
  var env: list<list<(ident, int)>> := [[]]
  handle(f)
    fun askEnv()
      match env
        Cons(e, _) -> e
        Nil -> throw("Tried to ask empty environment")
    fun pushEnv(e: list<(ident, int)>, x: ident, a: int)
      env := Cons(e.upsert(x, a), env)
      ()
    fun popEnv()
      match env
        Cons(_, e) -> env := e
        Nil -> throw("Tried to pop empty environment")

fun basicStore(f)
  var store := vector(1000, Nothing)
  var index := 0
  handle(f)
    fun find(i: int)
      match store.at(i)
        Just(Just(v)) -> v
        Nothing -> throw("Unbound store address " ++ i.show)
    fun alloc(x: ident)
      val a = index
      index := index + 1
      a
    fun extendStore(x, v)
      store[x] := Just(v)
      ()
    fun askStore()
      store