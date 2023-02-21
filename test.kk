import datastructure
import utils
import interp
import primitives

val eqI = Ident("eq")
val eqE = EVar(eqI)

val pE = eVar("p")
val qE = eVar("q")

fun primitiveTests()
  App(eEq, ETup([eChar('b'), eChar('b')])).eval.show.println
  App(eEq, ETup([eChar('b'), eChar('c')])).eval.show.println
  App(eEq, ETup([eInt(1), eInt(1)])).eval.show.println
  App(eEq, ETup([eInt(1), eInt(2)])).eval.show.println
  App(eEq, ETup([ETup([eInt(1), eChar('a')]), ETup([eInt(1), eChar('a')])])).eval.show.println
  App(eEq, ETup([ETup([eInt(1), eChar('a')]), ETup([eInt(2), eChar('b')])])).eval.show.println
  App(eAdd, ETup([eInt(1), eInt(2)])).eval.show.println
  App(eMult, ETup([eInt(1), eInt(2)])).eval.show.println
  App(eNeg, eInt(1)).eval.show.println
  App(eAdd, ETup([eFloat(1.5), eFloat(2.5)])).eval.show.println
  App(eMult, ETup([eFloat(1.5), eFloat(2.5)])).eval.show.println
  App(eNeg, eFloat(1.0)).eval.show.println

  val a = Ident("a")
  val eA = EVar(a)
  App(Lam(a, App(eA, ETup([eChar('b'), eChar('b')]))), eEq).eval.show.println

fun main()
  primitiveTests()
  ()

