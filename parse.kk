import std/os/file
import std/os/path
import std/text/parse
import std/num/float64
import datastructure
import utils

fun parseBool(): parse literal
  char('#')
  val s = [{char('t')}, {char('f')}].choose
  val x = if s == 't' then BoolL(True) else BoolL(False)
  x

fun parseChar(): parse literal
  char('\'')
  val c = alpha-num()
  char('\'')
  CharL(c)

fun parseFloat(): parse literal
  val f = pint()
  optional(FloatL(f.encode(0)))
    char('.')
    val n = pnat()
    match parse-float64(f.show ++ "." ++ n.show)
      Just(x) -> FloatL(x)
      Nothing -> fail("Not a float")


fun parseInt(): parse literal
  val i = pint()
  IntL(i)

fun parseLit(): parse expr
  ELit([parseInt, parseChar, parseBool].choose)

fun parseOperator(): parse ident
  Ident([{char-is("op", fn(c) c == '+' || c == '*' || c == '!').string}].choose)

fun parseIdent(): parse ident
  val st = char-is("ident start", fn(c) c.is-alpha || c == '_')
  val rest = alpha-num.many.string
  Ident(st.string ++ rest)

fun parseApp(): <div,parse> expr
  char('(')
  whitespace.many()
  val e0 = parseExpr()
  whitespace.many1()
  val e1 = (parseExpr || parseTuple)
  whitespace.many()
  char(')')
  App(e0, e1)

fun parseLam(): <div,parse> expr
  char('(')
  whitespace.many()
  pstring("λ")
  whitespace.many1()
  char('(')
  whitespace.many()
  val x = parseIdent()
  whitespace.many()
  char(')')
  whitespace.many1()
  val e = parseExpr()
  whitespace.many()
  char(')')
  Lam(x, e)

fun parseRec(): <div,parse> expr
  char('(')
  whitespace.many()
  pstring("rec")
  whitespace.many1()
  val x = parseIdent()
  whitespace.many1()
  val r = parseExpr()
  whitespace.many()
  Lam(x, r)

fun parseIf(): <div,parse> expr
  char('(')
  whitespace.many()
  pstring("if0")
  whitespace.many1()
  val e0 = parseExpr()
  whitespace.many1()
  val e1 = parseExpr()
  whitespace.many1()
  val e2 = parseExpr()
  whitespace.many()
  char(')')
  If(e0, e1, e2)

fun parseAssign(): <div,parse> expr
  char('(')
  whitespace.many()
  val r = parseExpr()
  whitespace.many1()
  pstring(":=")
  whitespace.many1()
  val e = parseExpr()
  whitespace.many()
  char(')')
  App(r, e)

fun parseComment(): parse string
  char-is("comment start", fn(x) x == ';')
  val c = chars-are("comment", fn(x) x != '\n' && x != '\r').string
  char-is("comment end", fn(x) x == '\n' || x == '\r')
  c

fun parseTuple(): <div,parse> expr
  val fst = parseExpr()
  val rst = many
    whitespace.many1()
    parseExpr()
  ETup(Cons(fst,rst))

fun parseExpr(): <div,parse> expr
  [parseLit, {EVar(parseIdent())}, {EVar(parseOperator())}, parseRec, parseLam, parseIf, parseAssign, parseApp].choose

fun parseProgram(): <div,parse> list<expr>
  whitespace.many()
  parseComment.many()
  whitespace.many()
  many1
    val x = parseExpr()
    whitespace.many()
    parseComment.many()  
    whitespace.many()
    x

fun parseScheme(file: string): <div,exn,fsys> parse-error<list<expr>>
  val f = read-text-file(file.path)
  f.trace
  with parse-eof(f.slice)
  parseProgram()

fun parseOrEmpty(s: string)
  val p = parseScheme(s)
  match p
    ParseOk(r) -> 
      r
    ParseError(_) -> 
      []

fun test()
  val p = parseScheme("examples/dead-ex0.rkt")
  trace("Done")
  match p
    ParseOk(s) -> 
      trace("Okay")
      s.map(showLisp).join("\n").println
    ParseError(e) -> 
      trace("Not Okay")
      e.println


// fun main()
//   test()
