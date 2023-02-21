
import datastructure
import utils
// Primitives

// Primitive Expresssions
fun doFst(v: evalue): exn evalue
  match v
    Tuple(Cons(c0, _)) -> c0
    _ -> throw("Invalid argument to fst")
fun doSnd(v: evalue): exn evalue
  match v
    Tuple(Cons(_, Cons(c1, _))) -> c1
    _ -> throw("Invalid argument to snd")
fun doThd(v: evalue): exn evalue
  match v
    Tuple(Cons(_, Cons(_, Cons(c2, _)))) -> c2
    _ -> throw("Invalid argument to thd")
fun doOr(v: evalue): exn evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 || b1)
    _ -> throw("Invalid argument to or")
fun doAnd(v: evalue): exn evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 && b1)
    _ -> throw("Invalid argument to and")
fun doEq(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Bool(i0 == i1)
    Tuple([Char(c0), Char(c1)]) -> Bool(c0 == c1)
    Tuple([Tuple(x1), Tuple(x2)]) -> 
      Bool(x1.zip(x2).all(fn((a, b)) -> doEq(Tuple([a, b]).unsafe-decreasing).getBool))
    _ -> throw("Invalid argument to eq")
fun doAdd(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 + i1)
    Tuple([Float(f0), Float(f1)]) -> Float(f0 + f1)
    Tuple([Tuple(x1)]) -> 
      match x1.head
        Just(Int(_)) -> x1.foldl(Int(0), fn(Int(a), Int(b)) Int(a + b))
        Just(Float(_)) -> x1.foldl(Float(0.0), fn(Float(a), Float(b)) Float(a + b))
        _ -> throw ("Invalid argument to add")
    _ -> throw("Invalid argument to add")
fun doMult(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 * i1)
    Tuple([Float(f0), Float(f1)]) -> Float(f0 * f1)
    Tuple([Tuple(x1)]) -> 
      match x1.head
        Just(Int(_)) -> x1.foldl(Int(1), fn(Int(a), Int(b)) Int(a * b))
        Just(Float(_)) -> x1.foldl(Float(1.0), fn(Float(a), Float(b)) Float(a * b))
        _ -> throw ("Invalid argument to mult")
    _ -> throw("Invalid argument to mult")
fun doNeg(v: evalue): exn evalue
  match v
    Int(i0) -> Int(0 - i0)
    Float(f0) -> Float(0.0 - f0)
    _ -> throw("Invalid argument to neg")
  
val eFst = PrimOp(Ident("fst"), doFst)
val eSnd = PrimOp(Ident("snd"), doSnd)
val eThd = PrimOp(Ident("thd"), doThd)
val eOr = PrimOp(Ident("or"), doOr)
val eAnd = PrimOp(Ident("and"), doAnd)
val eEq = PrimOp(Ident("eq"), doEq)
val eAdd = PrimOp(Ident("eAdd"), doAdd)
val eMult = PrimOp(Ident("eMult"), doMult)
val eNeg = PrimOp(Ident("eNeg"), doNeg)
val primExprs = [eFst, eSnd, eThd, eOr, eAnd, eEq, eAdd, eMult, eNeg]

fun lookupPrim(id2: ident): maybe<expr>
  with a <- primExprs.find
  match a
    PrimOp(id, _) | id.name == id2.name -> True
    _ -> False