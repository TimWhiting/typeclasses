import datastructure
import utils
import primitives

fun eval(x: expr, env: environment = []): <exn,console,div> evalue
  // (x.show() ++ " where bindings " ++ env.show()).println()
  val y = match x
    // Literals
    ELit(IntL(v)) -> Int(v)
    ELit(FloatL(v)) -> Float(v)
    ELit(CharL(v)) -> Char(v)
    ELit(BoolL(v)) -> Bool(v)
    ETup(v) -> Tuple(v.map(fn (vi) eval(vi,env)))
    // Primitive operations
    PrimOp(_, f) -> PrimClos(f)
    EVar(x1) -> 
      // trace(t.show)
      match lookupIdent(x1, env)
        Just((_, e)) -> e
        Nothing ->
          match lookupPrim(x1)
            Just(op) -> Clos(Ident("default"), op, env)
            _ -> throw("Unbound variable " ++ x1.name.show)
    Lam(x1, e1) -> Clos(x1, e1, env)
    Let(i, e0, e1) ->
      eval(e1, Cons((i, eval(e0, env)), env))
    App(e1, e2) -> 
      val f = eval(e1, env)
      val a = eval(e2, env)
      match f
        Clos(arg, body, cenv) -> eval(body, Cons((arg, a), cenv))
        PrimClos(f1) -> f1(a)
        _ -> throw("Non-function value in function position " ++ e1.show)
    _ -> throw("Not implemented yet " ++ x.show)
  y

fun lookupIdent(x: ident, env: environment): <> maybe<(ident,evalue)>
  env.find fn(a)
    unsafe-total
      a.fst == x
    