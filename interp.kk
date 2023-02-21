import datastructure
import utils
import primitives

effect store<a,v>
  fun alloc(x: ident): a // Address
  fun extend(x: a, v: v): () // Extend store
  fun find(i: a): v // Value
  fun askStore(): vector<maybe<v>> // Store

effect env<a, v>
  fun askEnv(): list<(ident,a)> // Environment
  fun pushEnv(e: list<(ident, a)>, x: ident, a: a): ()
  fun popEnv(): ()

effect handle-eval
  // fun askEnv(): list<(ident,a)> // Environment
  // ctl find(i: a): v // Value
  // fun alloc(x: ident): a // Address
  // fun extend(x: a, v: v): () // Extend store
  // fun pushEnv(e: list<(ident, a)>, x: ident, a: a): ()
  // fun popEnv(): ()
  fun doSomething(e: expr): ()

fun eval(x: expr): <exn,console,div,handle-eval,env<int,evalue>,store<int,evalue>> evalue
  doSomething(x)
  // (x.show() ++ " where bindings " ++ env.show()).println()
  val y = match x
    // Literals
    ELit(IntL(v)) -> Int(v)
    ELit(FloatL(v)) -> Float(v)
    ELit(CharL(v)) -> Char(v)
    ELit(BoolL(v)) -> Bool(v)
    ETup(v) -> Tuple(v.map(fn (vi) eval(vi)))
    // Primitive operations
    PrimOp(_, f) -> PrimClos(f)
    EVar(x1) -> 
      val e = askEnv()
      match e.getAddr(x1)
        Just(a) -> find(a)
        Nothing ->
          match lookupPrim(x1)
            Just(PrimOp(_, f)) -> PrimClos(f)
            Nothing -> throw("Unbound variable " ++ x.show ++ " in environment " ++ e.show)
    If(e0, e1, e2) ->
      match eval(e0)
        Bool(b) -> if b then eval(e1) else eval(e2)
        _ -> throw("Non-boolean value in if condition " ++ e0.show)
    Lam(x1, e1) -> Clos(x1, e1, askEnv())
    // Let(i, e0, e1) ->
    //   rho' = Cons((i, ev(e0)))
    //   ev(e1)
    App(e0, e1) -> 
      // trace("Applying " ++ e0.show ++ " to " ++ e1.show)
      val f = eval(e0)
      match f
        Clos(arg, body, cenv) -> 
          val v1 = eval(e1)
          val a = alloc(arg)
          extend(a, v1)
          pushEnv(cenv, arg, a)
          // trace("Pushed env evaluating body with " ++ arg.show ++ " bound to address " ++ a.show ++ " with value " ++ v1.show)
          val v = eval(body)
          // trace("Popping env")
          popEnv()
          v
        PrimClos(f1) -> 
          // trace("Evaluating arg for primitive closure")
          f1(eval(e1))
        _ -> throw("Non-function value in function position " ++ e1.show)
    _ -> throw("Not implemented yet " ++ x.show)
  y

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
  var store: vector<maybe<evalue>> := vector(1000, Nothing)
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
    fun extend(x: int, v: evalue)
      store[x] := Just(v)
      ()
    fun askStore()
      store

fun basicEval(xpr: expr): <exn,console,div> evalue
  with basicEnv
  with basicStore
  with handler
    fun doSomething(x: expr)
      ()
  eval(xpr)

fun traceEval(xpr: expr): <exn,console,div> string
  var l := []
  with basicEnv
  with basicStore
  with handler
    fun doSomething(x: expr)
      l := Cons("Evaluating expression " ++ x.showLisp ++ " with " ++ askEnv().show ++ " and " ++ askStore().show, l)
  eval(xpr)
  l.join("\n")
