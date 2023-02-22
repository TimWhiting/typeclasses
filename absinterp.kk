type eabsvalue
  IntV
  FloatV
  BoolV
  CharV
  Tuple2(x: list<eabsvalue>)
  PrimClos2(i: ident)
  Clos2(x: ident, e: expr, cenv: list<(ident, int)>)

fun abstractOp(i: ident): bool
  match i
    Ident("+") -> fn(_) IntV
    Ident("-") -> fn(_) IntV
    Ident("*") -> fn(_) IntV
    Ident("/") -> fn(_) IntV
    Ident("==") -> fn(_) BoolV
    Ident("||") -> fn(_) BoolV
    Ident("&&") -> fn(_) BoolV
    Ident("fst") -> doFst2
    Ident("snd") -> doSnd2
    Ident("thd") -> doThd2
    _ -> throw("Primitive operation not implemented " ++ i.show)

fun primExprAbstEval(xpr: expr): pure list<eabsvalue>
  with basicEnv
  with basicStore
  with handler
    return(x) [x]
    fun doSomething(x: expr)
      ()
    ctl zero(_)
      resume(False) ++ resume(True)
    fun primOp(i)
      abstractOp(i)
    fun intV(_)
      IntV
    fun floatV(_)
      FloatV
    fun charV(_)
      CharV
    fun boolV(_)
      BoolV
    fun tupleV(i)
      Tuple2(i)
    fun primClos(i)
      PrimClos2(i)
    fun closV(x, e, cenv)
      Clos2(x, e, cenv)
    fun getClosure(v)
      match v
        Clos2(x, e, cenv) -> Clos(x, e, cenv)
        PrimClos2(i) -> PrimClos(i)
  eval(xpr)

fun doFst2(v: eabsvalue): exn eabsvalue
  match v
    Tuple2(Cons(c0, _)) -> c0
    _ -> throw("Invalid argument to fst")
fun doSnd2(v: eabsvalue): exn eabsvalue
  match v
    Tuple2(Cons(_, Cons(c1, _))) -> c1
    _ -> throw("Invalid argument to snd")
fun doThd2(v: eabsvalue): exn eabsvalue
  match v
    Tuple2(Cons(_, Cons(_, Cons(c2, _)))) -> c2
    _ -> throw("Invalid argument to thd")
