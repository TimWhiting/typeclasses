
import datastructure
import utils

effect failure
  ctl fail(v: string): b
// Primitives

// Primitive Expresssions
fun doFst(v: evalue): failure evalue
  match v
    Tuple(Cons(c0, _)) -> c0
    _ -> fail("Invalid argument to fst")
fun doSnd(v: evalue): failure evalue
  match v
    Tuple(Cons(_, Cons(c1, _))) -> c1
    _ -> fail("Invalid argument to snd")
fun doThd(v: evalue): failure evalue
  match v
    Tuple(Cons(_, Cons(_, Cons(c2, _)))) -> c2
    _ -> fail("Invalid argument to thd")
fun doOr(v: evalue): failure evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 || b1)
    _ -> fail("Invalid argument to or")
fun doAnd(v: evalue): failure evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 && b1)
    _ -> fail("Invalid argument to and")
fun getBool(b: evalue): failure bool
  match b
    Bool(bl) -> bl
    _ -> fail("Not a bool")
fun doEq(v: evalue): failure evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Bool(i0 == i1)
    Tuple([Char(c0), Char(c1)]) -> Bool(c0 == c1)
    Tuple([Tuple(x1), Tuple(x2)]) -> 
      Bool(x1.zip(x2).all(fn((a:evalue, b:evalue)) -> doEq(Tuple([a, b]).unsafe-decreasing).getBool))
    _ -> fail("Invalid argument to eq")
fun doAdd(v: evalue): failure evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 + i1)
    Tuple([Float(f0), Float(f1)]) -> Float(f0 + f1)
    Tuple([Tuple(x1)]) -> 
      match x1.head
        Just(Int(_)) -> tryfail("Arguments to + not all ints", {x1.foldl(Int(0), fn(Int(a), Int(b)) Int(a + b))})
        Just(Float(_)) -> tryfail("Arguments to + not all floats", {x1.foldl(Float(0.0), fn(Float(a), Float(b)) Float(a + b))})
        _ -> fail("Invalid argument to add")
    _ -> fail("Invalid argument to add")
fun doMult(v: evalue): failure evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 * i1)
    Tuple([Float(f0), Float(f1)]) -> Float(f0 * f1)
    Tuple([Tuple(x1)]) -> 
      match x1.head
        Just(Int(_)) -> tryfail("Arguments to * not all ints", {x1.foldl(Int(1), fn(Int(a), Int(b)) Int(a * b))})
        Just(Float(_)) -> tryfail("Arguments to * not all floats", {x1.foldl(Float(1.0), fn(Float(a), Float(b)) Float(a * b))})
        _ -> fail ("Invalid argument to mult")
    _ -> fail("Invalid argument to mult")
fun doDiv(v: evalue): failure evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> if i1 == 0 then fail("Division by zero") else Int(i0 / i1)
    Tuple([Float(f0), Float(f1)]) -> if f1 == 0.0 then fail("Division by zero") else Float(f0 / f1)
    _ -> fail("Invalid argument to mult")
fun doNeg(v: evalue): failure evalue
  match v
    Int(i0) -> Int(0 - i0)
    Float(f0) -> Float(0.0 - f0)
    _ -> fail("Invalid argument to neg")
  
val eFst = PrimOp(Ident("fst"))
val eSnd = PrimOp(Ident("snd"))
val eThd = PrimOp(Ident("thd"))
val eOr = PrimOp(Ident("||"))
val eAnd = PrimOp(Ident("&&"))
val eEq = PrimOp(Ident("=="))
val eAdd = PrimOp(Ident("+"))
val eMult = PrimOp(Ident("*"))
val eNeg = PrimOp(Ident("-"))
val eDiv = PrimOp(Ident("/"))
val primExprs = [eFst, eSnd, eThd, eOr, eAnd, eEq, eAdd, eMult, eNeg, eDiv]

fun lookupPrim(id2: ident): maybe<expr>
  with a <- primExprs.find
  match a
    PrimOp(id) | id.name == id2.name -> True
    _ -> False

fun tryfail(v: string, f: () -> <exn> a): <failure> a
  try(f, fn (_) fail(v))