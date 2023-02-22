import datastructure
import utils
import interp
import primitives

val eqI = Ident("==")
val eqE = EVar(eqI)

val pE = eVar("p")
val qE = eVar("q")

fun primitiveTests()
  App(eEq, ETup([eChar('b'), eChar('b')])).basicEval.show.println
  App(eEq, ETup([eChar('b'), eChar('c')])).basicEval.show.println
  App(eEq, ETup([eInt(1), eInt(1)])).basicEval.show.println
  App(eEq, ETup([eInt(1), eInt(2)])).basicEval.show.println
  App(eEq, ETup([ETup([eInt(1), eChar('a')]), ETup([eInt(1), eChar('a')])])).basicEval.show.println
  App(eEq, ETup([ETup([eInt(1), eChar('a')]), ETup([eInt(2), eChar('b')])])).basicEval.show.println
  App(eAdd, ETup([eInt(1), eInt(2)])).basicEval.show.println
  App(eMult, ETup([eInt(1), eInt(2)])).basicEval.show.println
  App(eNeg, eInt(1)).basicEval.show.println
  App(eAdd, ETup([eFloat(1.5), eFloat(2.5)])).basicEval.show.println
  App(eMult, ETup([eFloat(1.5), eFloat(2.5)])).basicEval.show.println
  App(eNeg, eFloat(1.0)).basicEval.show.println

  val a = Ident("a")
  val eA = EVar(a)
  App(Lam(a, App(eA, ETup([eChar('b'), eChar('b')]))), eEq).basicEval.show.println
  //(* (+ 3 4) 9)
  App(eMult, ETup([App(eAdd, ETup([eInt(3), eInt(4)])), eInt(9)])).traceEval.println

  // Dead expr 
  If(eBool(False), eInt(1), eInt(2)).deadExprEval.println
  Lam(Ident("x"), eVar("x")).deadExprEval.println
  If(App(eDiv, ETup([eInt(1), eInt(0)])), eInt(2), eInt(3)).deadExprEval.println

fun main()
  primitiveTests()
  ()

