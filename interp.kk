import datastructure
import utils
import primitives
import eval
import parse
fun basicZero(x: evalue): faildiv bool
  match x
    Bool(b) -> !b
    Int(0) -> True
    Int(_) -> False
    _ -> fail("Unexpected value in if condition " ++ x.show)

fun basicPrimOp(x: ident): faildiv primop<evalue>
  match x
    Ident("+") -> doAdd
    Ident("-") -> doNeg
    Ident("*") -> doMult
    Ident("/") -> doDiv
    Ident("==") -> doEq
    Ident("||") -> doOr
    Ident("&&") -> doAnd
    Ident("fst") -> doFst
    Ident("snd") -> doSnd
    Ident("thd") -> doThd
    Ident("add1") -> doAddOne
    _ -> fail("Primitive operation not implemented " ++ x.show)

fun interpAbstraction(f)
  handle(f)
    fun zero(x)
      basicZero(x)
    fun primOp(i)
      basicPrimOp(i)
    fun intV(i)
      Int(i)
    fun floatV(i)
      Float(i)
    fun charV(i)
      Char(i)
    fun boolV(i)
      Bool(i)
    fun tupleV(i)
      Tuple(i)
    fun primClos(i)
      PrimClos(i)
    fun closV(x, e, cenv)
      Clos(x, e, cenv)
    fun getClosure(v)
      v

fun basicEval(xpr: expr): pure evalue
  with basicFail
  with basicEnv
  with basicStore
  with interpAbstraction
  with handler
    fun doSomething(x: expr)
      ()
  eval(xpr)

fun traceEval(xpr: expr): pure string
  var l := []  
  with basicFail
  with basicEnv
  with basicStore
  with interpAbstraction
  with handler
    fun doSomething(x: expr)
      l := Cons("Trace evaluation " ++ x.showLisp ++ " with " ++ askEnv().show ++ " and " ++ askStore().show, l)
  eval(xpr)
  l.join("\n")

fun deadExprEval(xpr: expr): pure string
  var l: list<expr> := []
  with handler
    final ctl fail(x)
      if l.is-empty then "No dead expressions in " ++ xpr.showLisp else
        "Dead exprs in " ++ xpr.showLisp ++ ": with result failure: " ++ x ++ "\n\t" ++ l.map(fn(xx) xx.showLisp).join("\n\t")
  with basicEnv
  with basicStore
  with interpAbstraction
  with handler
        fun doSomething(x: expr)
          l := l.set-union(x.subexps, (==))
          l := l.set-remove(x, (==))
  val result:evalue = eval(xpr)
  if l.is-empty then "No dead expressions in " ++ xpr.showLisp else
    "Dead exprs in " ++ xpr.showLisp ++ ": with result: " ++ result.show ++ "\n\t" ++ l.map(fn(x) x.showLisp).join("\n\t")


fun tests()
  val a = Ident("a")
  val eA = EVar(a)
  // Basic evaluation with a lambda
  App(Lam(a, App(eA, ETup([eChar('b'), eChar('b')]))), eEq).basicEval.show.println

  //(* (+ 3 4) 9)
  App(eMult, ETup([App(eAdd, ETup([eInt(3), eInt(4)])), eInt(9)])).traceEval.println

  // Dead expr 
  If(eBool(False), eInt(1), eInt(2)).deadExprEval.println
  Lam(Ident("x"), eVar("x")).deadExprEval.println
  If(App(eDiv, ETup([eInt(1), eInt(0)])), eInt(2), eInt(3)).deadExprEval.println


fun ptests()
  parseOrEmpty("examples/dead-ex0.rkt").map fn(x) 
    deadExprEval(x).println

fun main()
//   tests()
  ptests()
  ()