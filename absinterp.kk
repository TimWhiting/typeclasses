import datastructure
import utils
import primitives
import eval

type abvalue
  IntV(gen: bool, v: int)
  FloatV(gen: bool, v: float64)
  BoolV(gen: bool, v: bool)
  CharV(gen: bool, v: char)
  Tuple2(x: list<abvalue>)
  PrimClos2(i: ident)
  Clos2(x: ident, e: expr, cenv: list<(ident, int)>)

fun abstractOp(i: ident): faildiv primop<abvalue>
  match i
    Ident("+") -> 
      fn(x)
        match x
          Tuple2([IntV(g1, v1), IntV(g2, v2)]) -> if g1 || g2 then IntV(True, 0) else IntV(False, v1 + v2)
          _ -> fail("Invalid argument to +")
    Ident("-") -> 
      fn(x)
        match x
          IntV(g1, v1) -> if g1 then IntV(True, 0) else IntV(False, 0 - v1)
          _ -> fail("Invalid argument to -")
    Ident("*") ->
      fn(x)
        match x
          Tuple2([IntV(g1, v1), IntV(g2, v2)]) -> if g1 || g2 then IntV(True, 0) else IntV(False, v1 * v2)
          _ -> fail("Invalid argument to *")
    Ident("/") -> 
      fn(x)
        match x
          Tuple2([IntV(g1, v1), IntV(g2, v2)]) -> if g1 || g2 then IntV(True, 0) else IntV(False, v1 / v2)
          _ -> fail("Invalid argument to /")
    Ident("==") -> fn(_) BoolV(True, False)
    Ident("||") -> fn(_) BoolV(True, False)
    Ident("&&") -> fn(_) BoolV(True, False)
    Ident("fst") -> doFst2
    Ident("snd") -> doSnd2
    Ident("thd") -> doThd2
    _ -> fail("Primitive operation not implemented " ++ i.show)

fun primExprAbstEval(xpr: expr): pure list<abvalue>
  with basicFail
  with basicEnv
  with basicStore
  with handler
    fun doSomething(x: expr)
      ()
  with handler
    return(x) [x]
    ctl zero(_)
      resume(False) ++ resume(True)
    fun primOp(i)
      abstractOp(i)
    fun intV(v)
      IntV(False, v)
    fun floatV(v)
      FloatV(False, v)
    fun charV(v)
      CharV(False, v)
    fun boolV(v)
      BoolV(False, v)
    fun tupleV(i)
      Tuple2(i)
    fun primClos(i)
      PrimClos2(i)
    fun closV(x, e, cenv)
      Clos2(x, e, cenv)
    fun getClosure(v)
      v.closure
  eval(xpr)

fun closure(v: abvalue): failure evalue
  match v
    Clos2(x, e, cenv) -> Clos(x, e, cenv)
    PrimClos2(i) -> PrimClos(i)
    _ -> fail("Invalid argument to closure")

fun doFst2(v: abvalue): failure abvalue
  match v
    Tuple2(Cons(c0, _)) -> c0
    _ -> fail("Invalid argument to fst")

fun doSnd2(v: abvalue): failure abvalue
  match v
    Tuple2(Cons(_, Cons(c1, _))) -> c1
    _ -> fail("Invalid argument to snd")

fun doThd2(v: abvalue): failure abvalue
  match v
    Tuple2(Cons(_, Cons(_, Cons(c2, _)))) -> c2
    _ -> fail("Invalid argument to thd")

fun show(v: abvalue): div string
  match v
    IntV(g, i) -> "IntV(" ++ g.show ++ ", " ++ i.show ++ ")"
    FloatV(g, i) -> "FloatV(" ++ g.show ++ ", " ++ i.show ++ ")"
    BoolV(g, i) -> "BoolV(" ++ g.show ++ ", " ++ i.show ++ ")"
    CharV(g, i) -> "CharV(" ++ g.show ++ ", " ++ i.show ++ ")"
    Tuple2(i) -> "Tuple2(" ++ i.map(show).join(",") ++ ")"
    PrimClos2(i) -> "PrimClos2(" ++ i.show ++ ")"
    Clos2(x, e, cenv) -> "Clos2(" ++ x.show ++ ", " ++ e.show ++ ", " ++ cenv.show ++ ")"

fun main()
  App(eMult, ETup([App(eAdd, ETup([eInt(3), eInt(4)])), eInt(9)])).primExprAbstEval.map(show).join("\n").println
  "if".println
  If(eBool(True), eInt(3), eInt(4)).primExprAbstEval.map(show).join("\n").println