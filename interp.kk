import datastructure
import utils
import primitives
import eval

fun basicZero(x: evalue): pure bool
  match x
    Bool(b) -> !b
    Int(0) -> True
    Int(_) -> False
    _ -> throw("Unexpected value in if condiiton " ++ x.show)

fun basicPrimOp(x: ident): pure primop<evalue>
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
    _ -> throw("Primitive operation not implemented " ++ x.show)

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
  with basicEnv
  with basicStore
  with interpAbstraction
  with handler
    fun doSomething(x: expr)
      ()
  eval(xpr)

fun traceEval(xpr: expr): pure string
  var l := []
  with basicEnv
  with basicStore
  with interpAbstraction
  with handler
    fun doSomething(x: expr)
      l := Cons("Trace evaluation" ++ x.showLisp ++ " with " ++ askEnv().show ++ " and " ++ askStore().show, l)
  eval(xpr)
  l.join("\n")

fun deadExprEval(xpr: expr): pure string
  var l: list<expr> := []
  with basicEnv
  with basicStore
  with interpAbstraction
  val z = try(
    {
      handle({eval(xpr)})
        fun doSomething(x: expr)
          l := l.set-union(x.subexps, (==))
          l := l.set-remove(x, (==))
    }, fn (y)
      ErrorV(y.show)
    )
  "Dead exprs in " ++ xpr.showLisp ++ ": result: " ++ z.show ++ "\n\t" ++ l.map(fn(x) x.showLisp).join("\n\t")
