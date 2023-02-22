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

fun main()
  primitiveTests()
  ()

