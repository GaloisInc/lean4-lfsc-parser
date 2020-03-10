/-
A fledging LFSC paser written in Lean 4.

Copyright Galois, Inc, 2020
Maintainer: Joe Hendrix

Available for redistribution under Apache 2.0 license.

It can be run on a PLF file with `lean --run lfsc.lean <filename.plf>`
-/

import Init.Lean.Data.Position
import Init.Data.PersistentHashMap

namespace Array

def fromList {α} (l:List α) : Array α := l.foldl Array.push Array.empty

end Array


namespace HashMap

def fromList {α β} [Hashable α] [HasBeq α] : List (α × β) → HashMap α β :=
  let f (m:HashMap α β) (p : α × β) := m.insert p.fst p.snd;
  λl => l.foldl f HashMap.empty

end HashMap

namespace lfsc

/- A symbol in LFSC is currently just a string that doesn't contain whitespace or parens. -/
def Symbol := String

/- Variable name -/
def Var := Symbol

@[reducible]
def FamilyIndex := Nat

/- Family tag -/
structure Family :=
(name : Symbol)
(idx : FamilyIndex)

@[reducible]
def CtorIndex := Nat

/- Constructor tag -/
structure Ctor :=
(name : Symbol)
(idx : CtorIndex)

@[reducible]
def ProgArgIndex := Nat

/- A reference to a program argument. -/
structure ProgArg :=
(name : Symbol)
(tp : Family)
(idx : ProgArgIndex)

@[reducible]
def ProgramIndex := Nat

/- A reference to a program -/
structure Program :=
(name : Symbol)
(idx : ProgramIndex)

/- Print rest of arguments for slist below -/
def slistAux : List String → String
| [] => ")"
| h::r => " " ++ h ++ slistAux r

/- Print an sexpression with a list of strings as parameters. -/
def slist : List String → String
| [] => "()"
| h::r => "(" ++ h ++ slistAux r

@[reducible]
def VarLevel := Nat

inductive VExpr : Type
| ctorInst : Ctor → Array VExpr → VExpr
-- A variable that comes from a bit lambda
| checkvarRef : Nat → String → VExpr
-- A reference to a lambda , phi or match statementvariable
| varRef : VarLevel → String → VExpr
| letvarRef : VarLevel → String → VExpr
-- An integer literal
| intLit : Int → VExpr
| lambda : Symbol → VExpr → VExpr
| letExpr : Symbol → VExpr → VExpr → VExpr
| hole : VExpr

namespace VExpr

-- Pretty print an expression
partial
def reprAux : VExpr → String
| ctorInst c args =>
  if args.isEmpty then
    c.name
  else
    slist (c.name :: reprAux <$> args.toList)
| checkvarRef _ nm => nm
| varRef _ nm => nm
| letvarRef _ nm => nm
| intLit i => repr i
| lambda v x => slist ["\\", v, reprAux x]
| letExpr nm val x => slist ["@", nm, reprAux val, reprAux x]
| hole => "_"

instance : HasRepr VExpr := ⟨VExpr.reprAux⟩

partial
def pisubst : VExpr → Array VExpr → VExpr
| ctorInst c args, r => ctorInst c (args.map (λa => pisubst a r))
| checkvarRef lvl nm, _ => checkvarRef lvl nm
| varRef lvl nm, r =>
  if h : lvl < r.size then
    r.get ⟨lvl, h⟩
  else
    varRef (lvl-r.size) nm
| letvarRef lvl nm, _ => letvarRef (lvl-1) nm
| intLit i, _ => intLit i
| lambda v x, r => lambda v (pisubst x r)
| letExpr nm val x, r => letExpr nm (pisubst val r) (pisubst val r)
| hole, _ => hole

end VExpr

inductive CodeVal
| expr : VExpr → CodeVal
| call : Program → Array CodeVal → CodeVal

namespace CodeVal

-- Pretty print an expression
partial
def reprAux : CodeVal → String
| expr c => repr c
| call p args => slist (p.name :: args.toList.map reprAux)

instance : HasRepr CodeVal := ⟨reprAux⟩

partial
def pisubst: CodeVal → Array VExpr → CodeVal
| expr e, val => expr (e.pisubst val)
| call pgm args, val => call pgm (args.map (λa => a.pisubst val))

end CodeVal

structure Check :=
(program : Program)
(args : Array CodeVal)
(res : CodeVal)

namespace Check

instance : HasRepr Check := ⟨λc => slist ["^", slist (c.program.name :: repr <$> c.args.toList), repr c.res]⟩

partial
def pisubst (c:Check) (val:Array VExpr) : Check :=
  { program := c.program, args := c.args.map (λa => a.pisubst val), res := c.res.pisubst val }

end Check


-- Expression type for definitions and code.
inductive AExpr : Type
-- References a type family with the given arguments.
| fam : Family → Array VExpr → AExpr
-- A pi type with the argument and expression.
| pi : String → AExpr → AExpr → AExpr
| check : Option String → Check → AExpr → AExpr
-- A reference to a global type synonym with the given definition.
| ref : String → AExpr → AExpr

namespace AExpr

-- Pretty print an expression
partial
def reprAux : AExpr → String
| fam f args =>
  if args.isEmpty then
    f.name
  else
    slist (f.name :: args.toList.map repr)
| pi nm tp x => slist ["!", nm, reprAux tp, reprAux x]
| check (Option.some nm) chk x => slist ["!", nm, repr chk, reprAux x]
| check Option.none      chk x => slist ["!",     repr chk, reprAux x]
| ref nm _ => nm
--| ._, codeVar _ nm => nm

instance : HasRepr AExpr := ⟨reprAux⟩

partial
def pisubst : AExpr → Array VExpr → AExpr
| fam f args,     val => fam f (args.map (λa => a.pisubst val))
| pi nm tp v,     val => pi nm (tp.pisubst val) (v.pisubst val)
| check mnm tp v, val => check mnm (tp.pisubst val) (v.pisubst val)
| ref nm gtp,     _   => ref nm gtp

end AExpr

-- Expression type for definitions and code.
inductive KExpr : Type
-- Kind constructors
| type : KExpr
| pi : String → AExpr → KExpr → KExpr
| check : Option String → Check → KExpr → KExpr


namespace KExpr

-- Pretty print an expression
partial
def reprAux : KExpr → String
| type => "type"
| pi nm tp x => slist ["!", nm, repr tp, reprAux x]
| check (Option.some nm) chk x => slist ["!", nm, repr chk, reprAux x]
| check Option.none      chk x => slist ["!",     repr chk, reprAux x]

instance : HasRepr KExpr := ⟨reprAux⟩

partial
def pisubst : KExpr → Array VExpr → KExpr
| type, _ => type
| pi nm tp v, val => pi nm (tp.pisubst val) (pisubst v val)
| check mnm chk v, val => check mnm (chk.pisubst val) (pisubst v val)

end KExpr

/- A Pattern with list of argument.. -/
structure Pat :=
(ctor : Ctor)
(args : Array (String × AExpr))

namespace Pat

protected
partial
def repr (p:Pat) : String :=
  if p.args.size = 0 then
    p.ctor.name
  else
    slist (p.ctor.name :: (Prod.fst <$> p.args.toList))

instance : HasRepr Pat := ⟨Pat.repr⟩

end Pat

inductive Code
| ctor : Ctor → Array Code → Code
| casevar : VarLevel → String → Code
| letvar : Nat → String → Code
| progarg : ProgArg → Code
| codeIntLit : Int → Code
| matchStmt : Code →  Array (Pat × Code) → Option Code → Code
| doStmt : Array Code → Code
| letStmt : String → Nat → Code → Code → Code
| markvar : Nat → Code → Code
| ifequal : Code → Code → Code → Code → Code
| ifmarked : Nat → Code → Code → Code → Code
| mp_ifzero : Code → Code → Code → Code
| mp_ifneg : Code → Code → Code → Code
| fail : AExpr → Code
| call : Program → Array Code → Code

namespace Code

partial
def reprAux : Code → String
--| codeSym nm => nm
| ctor c a =>
  if a.isEmpty then
    c.name
  else
    slist (c.name :: a.toList.map reprAux)
| progarg p => p.name
| casevar _ nm => nm
| letvar _ nm  => nm
| codeIntLit i => repr i
| matchStmt e cases mdef =>
  let caseReprs := (λ(p : Pat × Code) => slist [repr p.fst, reprAux p.snd]) <$> cases.toList;
  let defReprs : List String :=
        match mdef with
        | Option.some c => [reprAux c]
        | Option.none => [];
  slist ("match" :: reprAux e :: caseReprs ++ defReprs)
| doStmt l => slist ("do" :: reprAux <$> l.toList)
| letStmt var _ d x => slist ["let", reprAux d, reprAux x]
| markvar idx x =>
  let fnm := if idx = 1 then "markvar" else ("markvar" ++ repr idx);
  slist [fnm, reprAux x]
| ifequal x y t f => slist ["ifequal", reprAux x, reprAux y, reprAux t, reprAux f]
| ifmarked idx x t f =>
  let fnm := if idx = 1 then "ifmarked" else ("ifmarked" ++ repr idx);
  slist [fnm, reprAux x, reprAux t, reprAux f]
| mp_ifzero n t f =>
  slist ["mp_ifzero", reprAux n, reprAux t, reprAux f]
| mp_ifneg n t f =>
  slist ["mp_ifneg", reprAux n, reprAux t, reprAux f]
| fail tp => slist ["fail", repr tp]
| call pgm args => slist (pgm.name :: args.toList.map reprAux)

instance : HasRepr Code := ⟨Code.reprAux⟩

end Code

inductive SomeExpr
| embedKind  (x:KExpr) : SomeExpr
| embedFam   (x:AExpr) : SomeExpr
| embedCheck (x:Check) : SomeExpr
| embedVal   (x:VExpr) : SomeExpr

namespace SomeExpr

-- Pretty print an expression
partial
def reprAux : SomeExpr  → String
| embedKind x  => repr x
| embedFam  x  => repr x
| embedCheck x => repr x
| embedVal  x  => repr x

instance : HasRepr SomeExpr := ⟨reprAux⟩

end SomeExpr

inductive CheckValue
| bigLambda (v:Symbol) (tp:AExpr) (x:CheckValue) : CheckValue
| letExpr (v:Symbol) (val:VExpr) (x:CheckValue) : CheckValue
| proof (v:SomeExpr) : CheckValue

namespace CheckValue

-- Pretty print an expression
partial
def reprAux : CheckValue → String
| bigLambda v tp x => slist ["%", v, repr tp, reprAux x]
| letExpr nm val x => slist ["@", nm, repr val, reprAux x]
| proof x => repr x

instance : HasRepr CheckValue := ⟨reprAux⟩

end CheckValue

inductive Command
| declareType (nm:Symbol) (tp:KExpr) : Command
| declareCtor (nm:Symbol) (tp:AExpr) : Command
| define (nm:Symbol) (v:SomeExpr) : Command
| program (nm:Symbol) (args : Array (Symbol × Family)) (ret : Family) (d : Code) : Command
| check (v:CheckValue) : Command

namespace Command

def ppArg : Symbol × Family → String
| (nm, f) => slist [nm, f.name]

protected
def reprAux : Command → String
| (declareType s tp) => slist ["declare", s, repr tp]
| (declareCtor s tp) => slist ["declare", s, repr tp]
| (define s tp) => slist ["declare", s, repr tp]
| (program s args ret d) => slist ["program", s, slist (ppArg <$> args.toList), ret.name, repr d]
| (check e) => slist ["check", repr e]

instance : HasRepr Command := ⟨Command.reprAux⟩

end Command

structure ParserContext :=
(source : String)
(input : String)
(fileMap : Lean.FileMap)

structure ParserState :=
(index : String.Pos)

/- Read to end-of-line -/
partial
def ParserContext.eol (ctx:ParserContext) : ParserState → ParserState
| s =>
  if ctx.input.atEnd s.index then
    s
  else
    let c := ctx.input.get s.index;
    if c = '\n' then
      { index := s.index + 1 }
    else
     ParserContext.eol { index := s.index + c.utf8Size.toNat }

/- Read to next token -/
partial
def ParserContext.next (ctx:ParserContext) : ParserState → ParserState
| s =>
  if ctx.input.atEnd s.index then
    s
  else
    let c := ctx.input.get s.index;
    if c = ';' then
      ParserContext.next (ctx.eol { index := s.index + 1})
    else if c.isWhitespace then
      ParserContext.next { index := s.index + c.utf8Size.toNat }
    else
      s

structure ParserError :=
(source : String)
(pos : Lean.Position)
(message : String)

namespace ParserError

def new (ctx:ParserContext) (s:ParserState) (msg:String) : ParserError :=
{ source := ctx.source, pos := ctx.fileMap.toPosition s.index, message := msg }

instance : HasRepr ParserError := ⟨λe => e.source ++ toString e.pos ++ ": " ++ e.message⟩

instance : Inhabited ParserError := ⟨{ source := "arbitrary", pos := arbitrary _, message := "default" }⟩

end ParserError

def Parser := ReaderT ParserContext (EStateM ParserError ParserState)

def Parser.run {α} (m:Parser α) (src:String) (s:String) : Except ParserError α :=
  let ctx := { ParserContext . source := src, input := s, fileMap := s.toFileMap };
  match (ReaderT.run m ctx) (ctx.next { index := 0 }) with
  | EStateM.Result.ok a _ => Except.ok a
  | EStateM.Result.error e _ => Except.error e

namespace Parser

protected
def orelse {α} (x y : Parser α) : Parser α := λctx s =>
  match x ctx s with
  | EStateM.Result.ok a s => EStateM.Result.ok a s
  | EStateM.Result.error e _ => y ctx s

instance {α} : HasOrelse (Parser α) := ⟨Parser.orelse⟩

instance {α} : Inhabited (Parser α) := inferInstanceAs (Inhabited (ParserContext → EStateM ParserError ParserState α))
instance : Functor Parser := inferInstanceAs (Functor (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : HasSeq  Parser := inferInstanceAs (HasSeq (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : HasSeqLeft  Parser := inferInstanceAs (HasSeqLeft (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : HasSeqRight  Parser := inferInstanceAs (HasSeqRight (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : HasBind Parser := inferInstanceAs (HasBind (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : HasPure Parser := inferInstanceAs (HasPure (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : Monad Parser := inferInstanceAs (Monad (ReaderT ParserContext (EStateM ParserError ParserState)))
instance : MonadState ParserState Parser :=
  inferInstanceAs (MonadState ParserState (ReaderT ParserContext (EStateM ParserError ParserState)))

end Parser

partial
def hasMore : Parser Bool
| ctx, s => EStateM.Result.ok (not (ctx.input.atEnd s.index)) s

def fail {α} (msg:String) : Parser α := λctx s =>
  EStateM.Result.error (ParserError.new ctx s msg) s

def peek : Parser Char
| ctx, s =>
  if ctx.input.atEnd s.index then
    fail "End of string" ctx s
  else
    EStateM.Result.ok (ctx.input.get s.index) s

def skip : Parser Unit
| ctx, s =>
  if ctx.input.atEnd s.index then
    fail "End of string" ctx s
  else
    let c := ctx.input.get s.index;
    EStateM.Result.ok () (ctx.next { index := s.index + c.utf8Size.toNat })

def char (e:Char) : Parser Unit
| ctx, s =>
  if ctx.input.atEnd s.index then
    fail "End of string" ctx s
  else
    let c := ctx.input.get s.index;
    if c = e then
      EStateM.Result.ok () (ctx.next { index := s.index + c.utf8Size.toNat })
    else
      fail ("char match " ++ repr e ++ " failed") ctx s

partial
def keywordAux (expected:String) : String.Pos → Parser Unit
| i, ctx, s =>
  if expected.atEnd i then
     EStateM.Result.ok () (ctx.next s)
  else
    let e := expected.get i;
    if ctx.input.atEnd s.index then
      fail "End of string" ctx s
    else
      let c := ctx.input.get s.index;
      if c = e then
        let sz := e.utf8Size.toNat;
        keywordAux (i + sz) ctx { index := s.index + sz }
      else
        fail "Match failed" ctx s

partial
def keyword (expected:String) : Parser Unit := keywordAux expected 0

def lparen : Parser Unit := char '('

def rparen : Parser Unit := char ')'

partial
def listRestAux {α} (m:Parser α) : Array α → Parser (Array α)
| prev => do
  c ← peek;
  if c = ')' then
    skip $> prev
  else
    m >>= λv => listRestAux (prev.push v)

/-- `listRest m` read values using `m` until we encounter right paren. -/
partial
def listRest {α} (m:Parser α) : Parser (Array α) := listRestAux m Array.empty

/-- `list m` reads an expression of the form '(' m* ')`. -/
partial
def list {α} (m:Parser α) : Parser (Array α) := do
  c ← peek;
  if c = '(' then
    skip *> listRest m
  else
    fail "Expected start of list"

-- Helper for `match1 below.
partial
def matchAux (r:Char → Bool) (b:String.Pos) : Parser String
| ctx, s =>
  if ctx.input.atEnd s.index then
    EStateM.Result.ok (ctx.input.extract b s.index) (ctx.next s)
  else
    let c := ctx.input.get s.index;
    if r c then
      matchAux ctx { index := s.index + c.utf8Size.toNat }
    else
      EStateM.Result.ok (ctx.input.extract b s.index) (ctx.next s)

-- Recognize longest string that starts with a character matching
-- `h` and is followed by any number of characters matching `r`.
def match1 (nm:String) (h:Char → Bool) (r:Char → Bool) : Parser String
| ctx, s =>
  if ctx.input.atEnd s.index then
    fail "End of string" ctx s
  else
    let c := ctx.input.get s.index;
    if h c then
      matchAux r s.index ctx { index := s.index + c.utf8Size.toNat }
    else
      fail ("Unexpected " ++ nm ++ " start character: " ++ repr c) ctx s

def symbol : Parser Symbol :=
  let h (c:Char) : Bool := c ≠ '(' ∧ c ≠ ')' ∧ not c.isWhitespace;
  match1 "symbol" h h

def isPosDigit (c:Char) : Bool := c.val ≥ '1'.val && c.val ≤ '9'.val

def nat : Parser Nat := String.toNat <$> match1 "nat" isPosDigit Char.isDigit

def isNat (s:String) : Bool := s.all Char.isDigit && s ≠ "" && (s = "0" || s.front ≠ '0')

def parens {α} (i:Parser α) : Parser α := do
  c ← peek;
  if c = '(' then
    skip *> i <* rparen
  else
    fail "Expected start of parenthesis"

inductive SExprStart
| openparen : SExprStart
| symbol : String → SExprStart

def sexprStart : Parser SExprStart := do
  c ← peek;
  if c = '(' then
    skip $> SExprStart.openparen
  else
    SExprStart.symbol <$> symbol

------------------------------------------------------------------------
-- LFSC specific stuff

@[reducible]
def CheckVarIndex := Nat

inductive EnvDef
-- A global type with the given name.
| famDecl (f:Family) (k:KExpr) : EnvDef
-- A constructor declared
| ctorDecl (c:Ctor) (tp:AExpr) : EnvDef
-- A global defined expression with the given expression
| defDecl (e:SomeExpr) : EnvDef
-- A program declared in a top-level program definition
| programDecl (p:Program) (args : Array (Symbol × Family)) (resultType : Family) : EnvDef
-- A variable declaration from a big lambda
| checkVarDecl (var:CheckVarIndex) (tp:AExpr) : EnvDef
-- A variable declared from a pi that is a programmatic check
| checkDecl  : EnvDef
-- A variable declaration from a pi
| pivarDecl (lvl:VarLevel) (tp:AExpr) : EnvDef
-- A variable declared in a label and having the given type.
| lambdavarDecl (lvl:VarLevel) (tp:AExpr) : EnvDef
-- A let declaration
| letDecl (lvl:VarLevel) (v:VExpr) : EnvDef
-- A program argument
| progarg : ProgArg → EnvDef
-- A program argument
| caseVar (lvl:VarLevel) (tp:AExpr) : EnvDef
-- A Program let
| codelet : VarLevel → Code → EnvDef

namespace EnvDef

def type : EnvDef → String
| famDecl _ _ => "family"
| ctorDecl _ _ => "constructor"
| defDecl _ => "define"
| programDecl _ _ _ => "program"
| checkVarDecl _ _ => "constant"
| pivarDecl _ _ => "pi variable"
| checkDecl => "check"
| lambdavarDecl _ _ => "lambda variable"
| letDecl _ _ => "let declaration"
| progarg _ => "program argument"
| caseVar _ _ => "case variable"
| codelet _ _ => "code let"

end EnvDef


structure ProgramInfo :=
(args : Array (Symbol × Family))
(ret : Family)
(code : Code)

structure GlobalEnvironment :=
(commands : List Command)
(globals : HashMap String EnvDef)
(families : Array KExpr)
(ctors : Array AExpr)
(programCount : Nat)

def mpz : Family := ⟨"mpz", 0⟩

def mp_add : Program := ⟨"mp_add", 0⟩
def mp_mul : Program := ⟨"mp_mul", 0⟩

namespace GlobalEnvironment

def init : GlobalEnvironment :=
  { commands := [],
    globals := HashMap.fromList
                 [("mpz",    EnvDef.famDecl mpz KExpr.type),
                  ("mp_add", EnvDef.programDecl mp_add (Array.fromList [("x",mpz), ("y", mpz)]) mpz),
                  ("mp_mul", EnvDef.programDecl mp_add (Array.fromList [("x",mpz), ("y", mpz)]) mpz)
                  ],
    families := Array.empty.push KExpr.type,
    ctors := Array.empty,
    programCount := 2
    }

def addCommand (e:GlobalEnvironment) (c:Command) : GlobalEnvironment :=
  { e with commands := c :: e.commands }

def insert (e:GlobalEnvironment) (nm:String) (d:EnvDef) : GlobalEnvironment :=
  { e with globals := e.globals.insert nm d }

def addFamily (e:GlobalEnvironment) (nm:String) (k:KExpr) (addCommand:Bool) : GlobalEnvironment :=
  let f : Family := ⟨nm,e.families.size⟩;
  { e with commands := if addCommand then Command.declareType nm k :: e.commands else e.commands,
           globals := e.globals.insert nm (EnvDef.famDecl f k),
           families := e.families.push k
           }

def addCtor (e:GlobalEnvironment) (nm:String) (tp:AExpr) : GlobalEnvironment :=
  let cmd := Command.declareCtor nm tp;
  let c : Ctor := ⟨nm,e.ctors.size⟩;
  { e with commands := cmd :: e.commands,
           globals := e.globals.insert nm (EnvDef.ctorDecl c tp),
           ctors := e.ctors.push tp
           }

def addProgramDecl (e:GlobalEnvironment) (nm:String) (args : Array (Symbol × Family)) (ret : Family)
: GlobalEnvironment :=
  let p : Program := ⟨nm,e.programCount⟩;
  { e with globals := e.globals.insert nm (EnvDef.programDecl p args ret),
  }

def find? (e:GlobalEnvironment) (nm:String) : Option EnvDef := e.globals.find? nm

def ctorType? (e:GlobalEnvironment) (c:Ctor) : Option AExpr := e.ctors.get? c.idx

end GlobalEnvironment

structure Environment :=
(global : GlobalEnvironment)
(locals  : PHashMap String EnvDef)
(varCnt : VarLevel)
(checkVarCnt : CheckVarIndex)
-- Bindings of variables
(ctx : Array VExpr)

namespace Environment

def new (env:GlobalEnvironment) : Environment :=
  { global := env
  , locals := PersistentHashMap.empty
  , varCnt := 0
  , checkVarCnt := 0
  , ctx := Array.empty
  }

-- Create environment for program
def code (env:GlobalEnvironment) (args : Array (String × Family)) : Environment :=
  let insArg (m :  PHashMap String EnvDef) (p : String × Family) :=
        let a : ProgArg := ⟨p.fst, p.snd, m.size⟩;
        m.insert p.fst (EnvDef.progarg a);
  { global := env
  , locals := args.foldl insArg PersistentHashMap.empty
  , varCnt := 0
  , checkVarCnt := 0
  , ctx := Array.empty
  }

def find? (e:Environment) (nm:String) : Option EnvDef :=
  match e.locals.find? nm with
  | Option.some d => Option.some d
  | Option.none => e.global.find? nm

def insertCheckVar (e:Environment) (nm:String) (tp:AExpr) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.checkVarDecl e.checkVarCnt tp),
           checkVarCnt := e.checkVarCnt + 1
           }

def insertPiVar (e:Environment) (nm:String) (tp:AExpr) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.pivarDecl e.varCnt tp),
           varCnt := e.varCnt + 1,
           ctx := e.ctx.push (VExpr.varRef e.varCnt nm)
           }

def insertCheck (e:Environment) (mnm:Option String) (tpc:Check) : Environment :=
  match mnm with
  | Option.none => e
  | Option.some nm =>
    { e with locals := e.locals.insert nm EnvDef.checkDecl,
           varCnt := e.varCnt + 1,
           ctx := e.ctx.push (VExpr.varRef e.varCnt nm)
           }

def insertLambdaVar (e:Environment) (nm:String) (tp:AExpr) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.lambdavarDecl e.varCnt tp),
           varCnt := e.varCnt + 1,
           ctx := e.ctx.push (VExpr.varRef e.varCnt nm)
           }

def insertLetDef (e:Environment) (nm:String) (v:VExpr) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.letDecl e.varCnt v),
           varCnt := e.varCnt + 1,
           ctx := e.ctx.push (VExpr.varRef e.varCnt nm)
           }

-- Add code let
def addLet (e:Environment) (nm:String) (d:Code) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.codelet e.varCnt d), varCnt := e.varCnt + 1 }

-- Add a match patterhn
def addMatchPat (e:Environment) (nm:String) (tp:AExpr) : Environment :=
  { e with locals := e.locals.insert nm (EnvDef.caseVar e.varCnt tp), varCnt := e.varCnt + 1 }

end Environment

def index : String → Parser Nat
| "" => pure 1
| idx =>
   let c := idx.toNat;
   if 1 ≤ c ∧ c ≤ 32 then
     pure c
   else
     fail ("Illegal index: " ++ idx)

def checkNoTypeArgs (f:Family) : KExpr → Parser Unit
| KExpr.type => pure ()
| KExpr.pi _ _ _ => fail $ "Expected arguments to " ++ f.name
| KExpr.check _ _ _ => fail $ "Expected arguments to " ++ f.name

def checkNoCtorArgs (c:Ctor) : AExpr → Parser Unit
| AExpr.fam _ _ => pure ()
| AExpr.pi _ _ _ => fail $ "Expected arguments to " ++ c.name
| AExpr.check _ _ _ => fail $ "Expected arguments to " ++ c.name
| AExpr.ref _ d => checkNoCtorArgs d

section
open Option

def EqEnv := Array AExpr -- Type for pi variables

partial
def vexprEq : VExpr → VExpr → Except String VExpr
| VExpr.ctorInst xc xa, VExpr.ctorInst yc ya =>
  if xc.idx ≠ yc.idx then
    Except.error  ("Incompatible constructors: " ++ xc.name ++ " " ++ yc.name)
  else do
    let f (i:Nat) (xa1:VExpr) : Except String VExpr :=
         match ya.get? i with
         | Option.none => Except.error "Unexpected array length"
         | Option.some ya1 => vexprEq xa1 ya1;
    za ← xa.mapIdxM f;
    pure (VExpr.ctorInst xc za)
| VExpr.checkvarRef xl xnm, VExpr.checkvarRef yl ynm =>
  if xl = yl then
    pure $ VExpr.checkvarRef xl xnm
  else
    Except.error $ "Incompatible check variables: " ++ xnm ++ " " ++ ynm
| VExpr.hole, y =>
  pure y
| x, VExpr.hole =>
  pure x
| VExpr.varRef xl xnm, VExpr.varRef yl ynm =>
  if xl = yl then
    pure $ VExpr.varRef xl xnm
  else
    Except.error $ "Incompatible variables: " ++ xnm ++ " " ++ ynm
| x, y =>
  Except.error ("Value mismatch -- found: " ++ repr x ++ ", expected: " ++ repr y)


partial
def vexprEqV : VExpr → Array VExpr → VExpr → Except String VExpr
| VExpr.ctorInst xc xa, yctx, VExpr.ctorInst yc ya =>
  if xc.idx ≠ yc.idx then
    Except.error  ("Incompatible constructors: " ++ xc.name ++ " " ++ yc.name)
  else do
    let f (i:Nat) (xa1:VExpr) : Except String VExpr :=
         match ya.get? i with
         | Option.none => Except.error "Unexpected array length"
         | Option.some ya1 => vexprEqV xa1 yctx ya1;
    za ← xa.mapIdxM f;
    pure (VExpr.ctorInst xc za)
| VExpr.checkvarRef xl xnm, yctx, VExpr.checkvarRef yl ynm =>
  if xl = yl then
    pure $ VExpr.checkvarRef xl xnm
  else
    Except.error $ "Incompatible check variables: " ++ xnm ++ " " ++ ynm
| VExpr.hole, yctx, y =>
  pure (y.pisubst yctx)
| x, _, VExpr.hole =>
  pure x
| x, yctx, VExpr.varRef yl ynm =>
  if h : yl < yctx.size then
    vexprEq x (yctx.get ⟨yl, h⟩)
  else
    Except.error ("Illegal ctx index: (" ++ repr yl ++ ", " ++ ynm ++ ") " ++ repr yctx.size)

--| env, VExpr.varRef xl xnm, yctx, VExpr.varRef yl ynm =>
--  if xl = yl then
--    pure $ VExpr.varRef xl xnm
--  else
--    Except.error $ "Incompatible variables: " ++ xnm ++ " " ++ ynm
| x, yctx, y =>
  Except.error $
    "Lazy value mismatch -- found: " ++ repr x ++ ", expected: " ++ repr (y.pisubst yctx)

partial
def aexprEqV : AExpr → Array VExpr → AExpr → Except String AExpr
| AExpr.fam xf xa, yctx, AExpr.fam yf ya => do
  if xf.idx ≠ yf.idx then
    Except.error  ("Incompatible families: " ++ xf.name ++ " " ++ yf.name)
  else do
    let f (i:Nat) (xa1:VExpr) : Except String VExpr :=
         match ya.get? i with
         | Option.none => Except.error "Unexpected array length"
         | Option.some ya1 => vexprEqV xa1 yctx ya1;
    za ← xa.mapIdxM f;
    pure (AExpr.fam xf za)
| AExpr.ref xnm xd, yctx, AExpr.ref ynm yd => do
  if xnm = ynm then
    pure (AExpr.ref xnm xd)
  else
    aexprEqV xd Array.empty yd
| x, yctx, AExpr.ref ynm yd => aexprEqV x Array.empty yd
| AExpr.ref xnm xd, yctx, y => aexprEqV xd yctx y
| x, yctx, y =>
  Except.error ("Family mismatch -- found: " ++ repr x ++ ", expected: " ++ repr y)

end

partial
def asPi : Array VExpr → AExpr → Option (Array VExpr × String × AExpr × AExpr)
| _, AExpr.fam _ _ => Option.none
| yctx, AExpr.pi nm a r => Option.some (yctx, nm, a, r)
| _, AExpr.check _ _ _ => Option.none
| yctx, AExpr.ref _ x => asPi Array.empty x

def checkIntLitType (tpctx : Array VExpr) (tp:AExpr) : Parser Unit :=
  match aexprEqV (AExpr.fam mpz Array.empty) tpctx tp with
  | Except.error e => fail $ "Integer literal must have type mpz: " ++ e
  | Except.ok _ => pure ()

inductive ExprCtx
| Fam : ExprCtx
-- This parsed expressions of type `nm type`, `nm (^ .. ..)`, and `(^ .. ..).
| FamCheck : ExprCtx
-- @Value prev r@ produces a value with type @r.pisubst prev@.
| Value : Array VExpr → AExpr → ExprCtx
-- Code with the given value expected.
| codeVal : Family → ExprCtx
-- Any expression
| Any : ExprCtx
-- Current level of expression in tp and type
| TypeArgs (prev:Array VExpr) (tp:KExpr) : ExprCtx
-- `CtorArgs p r` parse a constructor with previous arguments `p`,
-- and remaining type `r`.
| CtorArgs (prev:Array VExpr) (tp:AExpr) : ExprCtx

inductive FamCheckRes
| arg : String → AExpr → FamCheckRes
| check : Option String → Check → FamCheckRes

namespace ExprCtx

@[reducible]
def result : ExprCtx → Type
| Fam => AExpr
| FamCheck => FamCheckRes
| Value _ _ => VExpr
-- Map to value and arguments to family
| codeVal f => CodeVal
| Any => SomeExpr
| TypeArgs _ _ => Array VExpr
| CtorArgs _ _ => Array VExpr × AExpr

end ExprCtx

open ExprCtx
open SomeExpr

partial
def matchFamily (expected:Family) : AExpr → Parser (Array VExpr)
| AExpr.fam f args =>
  if f.idx = expected.idx then
    pure args
  else
    fail $ "Did not match expected type " ++ expected.name
| AExpr.pi _ _ _ =>
  fail $ "Pi encountered when family expected: " ++ expected.name
| AExpr.check _ _ _ =>
  fail $ "Check encountered when family expected: " ++ expected.name
| AExpr.ref _ d => matchFamily d

partial
def expr : ∀(c:ExprCtx) (env:Environment), Parser (ExprCtx.result c)
| TypeArgs prev KExpr.type, env => do
  rparen $> prev
| TypeArgs prev (KExpr.pi nm tp r), env => do
  v ← expr (Value prev tp) env;
  expr (TypeArgs (prev.push v) r) env
| TypeArgs prev (KExpr.check _ _ r), env =>
  expr (TypeArgs prev r) env

| CtorArgs prev (AExpr.fam f args), env => do
  rparen $> (prev, AExpr.fam f args)
| CtorArgs prev (AExpr.pi _nm tp r), env => do
  v ← expr (Value prev tp) env;
  expr (CtorArgs (prev.push v) r) env
| CtorArgs prev (AExpr.check _ _ r), env => do
  expr (CtorArgs prev r) env
| CtorArgs prev (AExpr.ref _ d), env => do
  expr (CtorArgs prev d) env

| Fam, env => do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    c ← peek;
    match c with
    -- Pi variable
    | '!' => do
       skip;
       r ← expr FamCheck env;
       match r with
       | FamCheckRes.arg nm tp => do
         val ← expr Fam (env.insertPiVar nm tp) <* rparen;
         pure $ AExpr.pi nm tp val
       | FamCheckRes.check mnm chk => do
         val ← expr Fam (env.insertCheck mnm chk) <* rparen;
         pure $ AExpr.check mnm chk val
    | _ => do
      sym ← symbol;
      match env.find? sym with
      | Option.some (EnvDef.famDecl f k) =>
         AExpr.fam f <$> expr (TypeArgs Array.empty k) env
      | Option.none   => fail $ "Unknown type app symbol: " ++ sym
      | Option.some _ => fail $ "Expected type: " ++ sym
  | SExprStart.symbol sym => do
    match env.find? sym with
    | Option.none => fail $ "Unknown type single symbol: " ++ sym
    | Option.some (EnvDef.famDecl f k) => do
      checkNoTypeArgs f k $> AExpr.fam f Array.empty
    | Option.some _ => fail $ "Expected type: " ++ sym
| FamCheck, env => do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    c ← peek;
    if c  = '^' then do
      skip;
      lparen;
      pgmName ← symbol;
      match env.find? pgmName with
      | Option.some (EnvDef.programDecl pgm argTypes resType) => do
        let f (a : Symbol × Family) : Parser CodeVal := expr (codeVal a.snd) env;
        args ← argTypes.mapM f <* rparen;
        res  ← expr (codeVal resType) env;
        let chk : Check := { program := pgm, args := args, res := res };
        rparen $> FamCheckRes.check Option.none chk
      | _ => fail $ "Unknown program: " ++ pgmName
    else
      fail $ "Expected check"
  | SExprStart.symbol var => do
    c ← sexprStart;
    match c with
    | SExprStart.openparen => do
      c ← peek;
      match c with
      -- A Pi variable
      | '!' => do
        skip;
        r ← expr FamCheck env;
        match r with
        | FamCheckRes.arg nm tp => do
          val ← expr Fam (env.insertPiVar nm tp) <* rparen;
          pure $ FamCheckRes.arg var (AExpr.pi nm tp val)
        | FamCheckRes.check mnm chk => do
          val ← expr Fam (env.insertCheck mnm chk) <* rparen;
          pure $ FamCheckRes.arg var (AExpr.check mnm chk val)
      | '^' => do
        skip;
        lparen;
        sym ← symbol;
        match env.find? sym with
        | Option.some (EnvDef.programDecl pgm argTypes resType) => do
          let f (a : Symbol × Family) : Parser CodeVal := expr (codeVal a.snd) env;
          args ← argTypes.mapM f <* rparen;
          res ← expr (codeVal resType) env;
          let chk : Check := { program := pgm, args := args, res := res };
          rparen $> FamCheckRes.check (Option.some var) chk
        | _ => fail $ "Unknown program: " ++ sym
      | _ => do
        sym ← symbol;
        match env.find? sym with
        | Option.none => fail ("Unknown family or check function: " ++ sym)
        | Option.some (EnvDef.famDecl f k) =>
          (λr => FamCheckRes.arg var (AExpr.fam f r)) <$> expr (TypeArgs Array.empty k) env
        | Option.some _ =>
          fail $ "Expected type: " ++ sym
    | SExprStart.symbol sym =>
      match env.find? sym with
      | Option.some (EnvDef.famDecl f k) =>
        checkNoTypeArgs f k $> FamCheckRes.arg var (AExpr.fam f Array.empty)
      | Option.none   => fail $ "Unknown family of check constant: " ++ sym
      | Option.some _ => fail $ "Expected type: " ++ sym
| Value tpctx tp, env => do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    c ← peek;
    match c with
    -- Pi term
    | '!' => fail "Did not expect a type"
    -- Type annotation
    | ':' => do
      skip;
      annType ← expr Fam env;
      match aexprEqV annType tpctx tp with
      | Except.error e => fail e
      | Except.ok ztp => expr (Value env.ctx ztp) env <* rparen
     -- Let expression
    | '@' => do
       skip;
       nm ← symbol;
       da ← expr Any env;
       d ← match da with
           | embedVal v => pure v
           | _ => fail $ "Expected let value: " ++ repr da;
       val ← expr (Value tpctx tp) (env.insertLetDef nm d);
       rparen $> VExpr.letExpr nm d val
    -- Lambda
    | '\\' => do
       skip;
       match asPi tpctx tp with
       | Option.none => fail "Lambda encountered when function not expected."
       | Option.some (pictx, anm, atp,rtp) => do
         nm ← symbol;
         let v := VExpr.varRef pictx.size anm;
         rhs ← expr (Value (pictx.push v) rtp) (env.insertLambdaVar nm atp);
         rparen $> VExpr.lambda nm rhs
    | '~' => do
       skip;
       checkIntLitType tpctx tp;
       (λ(n:Nat) => VExpr.intLit (HasNeg.neg (Int.ofNat n))) <$> nat
    | _ => do
       sym ← symbol;
       match env.find? sym with
       | Option.none => fail ("Unknown typed function: " ++ sym)
       | Option.some (EnvDef.ctorDecl c ctorType) => do
          l ← expr (CtorArgs Array.empty ctorType) env;
          pure (VExpr.ctorInst c l.fst)
       | Option.some d => do
          fail (d.type ++ " unsupported as " ++ repr tp ++ " function:" ++ sym)
  | SExprStart.symbol sym =>
    if sym =  "_" then
      pure VExpr.hole
    else if isNat sym then do
      checkIntLitType tpctx tp;
      pure $ VExpr.intLit (Int.ofNat sym.toNat)
    else
      match env.find? sym with
      | Option.none => fail ("Unknown typed constant: " ++ sym ++ " " ++ repr tp)
      | Option.some (EnvDef.ctorDecl c ctorType) => do
        checkNoCtorArgs c ctorType;
        match aexprEqV ctorType tpctx tp with
        | Except.error e => fail $ "Ctor failed: " ++ e
        | Except.ok ztp => pure $ VExpr.ctorInst c Array.empty
      | Option.some (EnvDef.checkVarDecl lvl cvarType) => do
        match aexprEqV cvarType tpctx tp with
        | Except.error e => fail e
        | Except.ok ztp => pure $ VExpr.checkvarRef lvl sym
      | Option.some (EnvDef.defDecl val) => do
         -- FIXME: Check type of definition
         match val with
         | embedVal x => pure x
         | _ => fail $ "Unsupported value definition: " ++ sym
      | Option.some (EnvDef.pivarDecl lvl varType) => do
        match aexprEqV varType tpctx tp with
        | Except.error e => fail $ "Pi var failed: " ++ e ++ "\n"
                                ++ repr varType ++ " " ++ repr tp ++ " " ++ repr tpctx.size
        | Except.ok  ztp => pure $ VExpr.varRef lvl sym
      | Option.some (EnvDef.lambdavarDecl lvl vtp) => do
        match aexprEqV vtp tpctx tp with
        | Except.error e => fail e
        | Except.ok ztp => pure $ VExpr.varRef lvl sym
      | Option.some (EnvDef.letDecl lvl vtp) => do
         pure $ VExpr.letvarRef lvl sym
      | Option.some d =>
        fail $ d.type ++ " unsupported as " ++ repr tp ++ " constant: " ++ sym
| Any, env => do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    c ← peek;
    match c with
    -- Pi term
    | '!' => do
       skip;
       r ← expr FamCheck env;
       match r with
       | FamCheckRes.arg nm tp => do
         val ← expr Any (env.insertPiVar nm tp) <* rparen;
         match val with
         | embedKind k => pure $ embedKind $ KExpr.pi nm tp k
         | embedFam  d => pure $ embedFam  $ AExpr.pi nm tp d
         | _ => fail $ "Expected kind or type: " ++ repr val
       | FamCheckRes.check mnm chk => do
         val ← expr Any (env.insertCheck mnm chk) <* rparen;
         match val with
         | embedKind k => pure $ embedKind $ KExpr.check mnm chk k
         | embedFam  d => pure $ embedFam  $ AExpr.check mnm chk d
         | _ => fail $ "Expected kind or type: " ++ repr val
    -- Type annotation
    | ':' => do
       skip;
       annType ← expr Fam env;
       embedVal <$> expr (Value env.ctx annType) env <* rparen
    -- Let expression
    | '@' => do
       skip;
       nm ← symbol;
       da ← expr Any env;
       d ← match da with
           | embedVal v => pure v
           | _ => fail $ "Expected let value: " ++ repr da;
       va ← expr Any (env.insertLetDef nm d);
       rparen;
       match va with
       | embedVal v => pure (embedVal (VExpr.letExpr nm d v))
       | _ => fail $ "Expected let rhs: " ++ repr va
    -- Lambda
    | '\\' => do
       fail "Lambda can only appear when type is known."
    -- Check
    | '^' => do
       skip;
       lparen;
       sym ← symbol;
       match env.find? sym with
       | Option.some (EnvDef.programDecl pgm argTypes resType) => do
         let f (a : Symbol × Family) : Parser CodeVal := expr (codeVal a.snd) env;
         args ← argTypes.mapM f;
         rparen;
         res ← expr (codeVal resType) env;
         let chk : Check := { program := pgm, args := args, res := res };
         rparen $> embedCheck chk
       | _ => fail ("Unknown program: " ++ sym)
    | '~' => skip *> (λ(n:Nat) => embedVal (VExpr.intLit (HasNeg.neg (Int.ofNat n)))) <$> nat
    | _ => do
       sym ← symbol;
       match env.find? sym with
       | Option.none => fail ("Unknown untyped function: " ++ sym)
       | Option.some (EnvDef.famDecl f k) => do
          (λr => embedFam (AExpr.fam f r)) <$> expr (TypeArgs Array.empty k) env
       | Option.some (EnvDef.ctorDecl c ctorType) => do
          l ← expr (CtorArgs Array.empty ctorType) env;
          pure (embedVal (VExpr.ctorInst c l.fst))
       | Option.some d =>
         fail $ d.type ++ " unsupported as function: " ++ sym
  | SExprStart.symbol sym => do
    match sym with
    | "type" => pure $ embedKind KExpr.type
    | "_" => pure $ embedVal VExpr.hole
    | _ => do
      match env.find? sym with
      | Option.none => fail ("Unknown untyped constant: " ++ sym)
      | Option.some (EnvDef.famDecl f k) =>
        checkNoTypeArgs f k $> embedFam (AExpr.fam f Array.empty)
      | Option.some (EnvDef.ctorDecl c ctorType) => do
        checkNoCtorArgs c ctorType;
        pure $ embedVal (VExpr.ctorInst c Array.empty)
      | Option.some (EnvDef.defDecl val) => do
         match val with
         | embedFam x => pure $ embedFam $ AExpr.ref sym x
         | _ => fail ("Unsupported definition: " ++ sym)
      | Option.some (EnvDef.checkVarDecl lvl tp) => do
        pure $ embedVal $ VExpr.checkvarRef lvl sym
      | Option.some (EnvDef.pivarDecl lvl tp) => do
        pure $ embedVal $ VExpr.varRef lvl sym
      | Option.some (EnvDef.lambdavarDecl lvl tp) => do
        pure $ embedVal $ VExpr.varRef lvl sym
      | Option.some d =>
        fail $ d.type ++ " unsupported as constant: " ++ sym
| codeVal expected, env => do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    c ← peek;
    match c with
    -- Pi term
    | '!' => fail "Unexpected pi term"
    -- Type annotation
    | ':' => fail "Unexpected type annotation"
    -- Let expression
    | '@' => fail "Unexpected let expression"
    | '\\' => fail "Unexpected lambda expression."
    | '^' => fail "Family expected instead of check"
    | '~' => fail "Family expected instead of int literal"
    | _ => do
       sym ← symbol;
       match env.find? sym with
       | Option.some (EnvDef.programDecl pgm argTypes resType) => do
         let f (a : Symbol × Family) : Parser CodeVal := expr (codeVal a.snd) env;
         args ← argTypes.mapM f <* rparen;
         when (expected.idx ≠ resType.idx) $ fail "Program type mismatch";
         pure $ CodeVal.call pgm args

       | Option.some d =>
         fail $ d.type ++ " unsupported as code function: " ++ sym
       | Option.none =>
         fail $ "Unknown untyped function: " ++ sym
  | SExprStart.symbol sym =>
    match sym with
    | "type" => fail "type not expected"
    | "_" => fail "hole not expected"
    | _ =>
      match env.find? sym with
      | Option.some (EnvDef.ctorDecl c ctorType) => do
        args ← matchFamily expected ctorType;
        when (args.size > 0) $ fail $ "Expected arguments.";
        pure $ CodeVal.expr (VExpr.ctorInst c Array.empty)
      | Option.some (EnvDef.pivarDecl lvl tp) => do
        _ ← matchFamily expected tp;
        pure $ CodeVal.expr (VExpr.varRef lvl sym)
      | Option.some d =>
        fail $ d.type ++ " unsupported as code constant: " ++ sym
      | Option.none => fail $ "Unknown untyped constant: " ++ sym

partial
def patVars : Array (String × AExpr)
            → Environment
            → AExpr
            → Parser (Array (String × AExpr) × Environment × AExpr)
| prev, env, AExpr.fam f args =>
  rparen $> (prev, env, AExpr.fam f args)
| prev, env, AExpr.pi nm tp r => do
  nm ← symbol;
  let v := VExpr.varRef env.varCnt nm;
  let env' := env.addMatchPat nm tp;
  patVars (prev.push (nm,tp)) env' r
| prev, env, AExpr.check _ _ r => do
  patVars prev env r
| prev, env, AExpr.ref _ d => do
  patVars prev env d

def patternOrDefault (env:Environment) : Parser (Option (Pat × Environment)) := do
  c ← sexprStart;
  match c with
  | SExprStart.openparen => do
    sym ← symbol;
    match env.find? sym with
    | Option.some (EnvDef.ctorDecl c ctorType) => do
      (vars,env', rtp) ← patVars Array.empty env ctorType;
      pure (Option.some ({ ctor := c, args := vars }, env'))
    | _ => do
      fail ("Could not find constructor: " ++ sym)
  | SExprStart.symbol "default" =>
    pure $ Option.none
  | SExprStart.symbol sym => do
    match env.find? sym with
    | Option.some (EnvDef.ctorDecl c corType) => do
      pure $ Option.some ({ ctor := c, args := Array.empty }, env)
    | _ => do
      fail ("Could not find constructor: " ++ sym)

inductive CodeReq
| anyCode : CodeReq
| ctorArgs : Array Code → Nat → AExpr → CodeReq

namespace CodeReq

def type : CodeReq → Type
| anyCode => Code
| ctorArgs _ _ _ => Array Code × Nat × Family × Array VExpr

end CodeReq

open CodeReq

partial
def matchRest (env:Environment) (e:Code) (m : Environment → Parser Code) : Array (Pat × Code) → Parser Code
| prev => do
   c ← peek;
   match c with
   | '(' => do
     skip;
     mp ← patternOrDefault env;
     match mp with
     | Option.some (p,env') => do
       v ← m env';
       rparen;
       matchRest (prev.push (p,v))
     | Option.none => do
       v ← m env;
       rparen;
       rparen $> Code.matchStmt e prev (Option.some v)
   | ')' => skip $> Code.matchStmt e prev Option.none
   | _ => fail "Expected match case"

partial
def code : ∀(ctx:CodeReq), Environment → Parser ctx.type
| ctorArgs prev n (AExpr.fam f args), env => do
  rparen $> (prev, n, f, args)
| ctorArgs prev n (AExpr.pi nm tp r ), env => do
  v ← code anyCode env;
  code (ctorArgs (prev.push v) (n+1) r) env
| ctorArgs prev n (AExpr.check _ _ r), env =>
  -- TODO Add some notion of check here
  code (ctorArgs prev n r) env
| ctorArgs prev _ (AExpr.ref _ d), env =>
  code (ctorArgs prev 0 d) env
| anyCode, env => do
  c ← peek;
  match c with
  | '(' => do
    skip;
    c ← peek;
    match c with
    | '~' => skip *> (λ(n:Nat) => Code.codeIntLit (HasNeg.neg (Int.ofNat n))) <$> nat <* rparen
    | _ => do
      sym ← symbol;
      if sym = "ifequal" then do
        (Code.ifequal <$> code anyCode env <*> code anyCode env <*> code anyCode env <*> code anyCode env) <* rparen
      else if sym = "match" then do
        code anyCode env >>= λe => matchRest env e (code anyCode) Array.empty
      else if sym = "do" then do
        Code.doStmt <$> listRest (code anyCode env)
      else if sym = "let" then do
        nm ← symbol;
        let idx := env.varCnt;
        symdef ← code anyCode env;
        rest ← code anyCode (env.addLet nm symdef);
        rparen $> Code.letStmt nm idx symdef rest
      else if sym = "fail" then do
        Code.fail <$> expr Fam env <* rparen
      else if "markvar".isPrefixOf sym then do
        let rest := sym.drop "markvar".length;
        Code.markvar <$> index rest <*> code anyCode env <* rparen
       else if "ifmarked".isPrefixOf sym then do
         let rest := sym.drop "ifmarked".length;
         (Code.ifmarked <$> index rest <*> code anyCode env <*> code anyCode env <*> code anyCode env) <* rparen
       else if sym = "mp_ifzero" then do
          c ← code anyCode env;
          t ← code anyCode env;
          f ← code anyCode env;
         rparen $> Code.mp_ifzero c t f
       else if sym = "mp_ifneg" then do
          c ← code anyCode env;
          t ← code anyCode env;
          f ← code anyCode env;
         rparen $> Code.mp_ifneg c t f
       else do
         match env.find? sym with
         | Option.none => fail $ "Unknown code function symbol: " ++ sym
         | Option.some (EnvDef.ctorDecl c ctorType) => do
           ⟨l,_,_⟩ ← code (ctorArgs Array.empty 0 ctorType) env;
           pure (Code.ctor c l)
         | Option.some (EnvDef.programDecl p args res) => do
           argValues ← args.mapM (λ⟨nm,f⟩ => code anyCode env);
           rparen;
           pure (Code.call p argValues)
         | Option.some d => fail $ d.type ++ " unsupported as code function: " ++ sym
-- Code.ctor sym <$> listRest (code env)
  | _ => do
    sym ← symbol;
    match env.find? sym with
    | Option.none => fail $ "Unknown symbol: " ++ sym
    | Option.some (EnvDef.progarg p) => pure $ Code.progarg p
    | Option.some (EnvDef.caseVar lvl tp) => pure $ Code.casevar lvl sym
    | Option.some (EnvDef.ctorDecl c ctorType) => do
        checkNoCtorArgs c ctorType;
        pure (Code.ctor c Array.empty)
    | Option.some (EnvDef.codelet v _) => do
        pure (Code.letvar v sym)
    | Option.some d => fail $ d.type ++ " unsupported as code: " ++ sym

--Code.codeSym <$> symbol

partial
def checkValue : Environment → Parser CheckValue
| env => do
  s ← get;
  c ← peek;
  if c == '(' then do
    skip;
    c ← peek;
    match c with
    | '%' => do
       skip;
       nm ← symbol;
       tp ← expr Fam env;
       r ← checkValue (env.insertCheckVar nm tp);
       rparen;
       pure (CheckValue.bigLambda nm tp r)
    -- Let
    | '@' => do
       skip;
       nm ← symbol;
       da ← expr Any env;
       d ← match da with
           | embedVal v => pure v
           | _ => fail $ "Expected let value: " ++ repr da;
       x ← checkValue (env.insertLetDef nm d);
       rparen $> CheckValue.letExpr nm d x
    | _ => do set s; CheckValue.proof <$> expr Any env
  else
    CheckValue.proof <$> expr Any env

partial
def familyName (env:GlobalEnvironment) : Parser Family := do
  sym ← symbol;
  match env.find? sym with
  | Option.none => fail $ "Unknown symbol: " ++ sym
  | Option.some (EnvDef.famDecl f k) => pure f
  | Option.some _ =>  fail $ "Expected family: " ++ sym

partial
def command : GlobalEnvironment → Parser GlobalEnvironment
| genv => do
  c ← peek;
  if c = '(' then do
    skip;
    h ← symbol;
    match h with
    | "declare" => do
      nm ← symbol;
      let env := Environment.new genv;
      e ← expr Any env <* rparen;
      match e with
      | embedKind k => pure (genv.addFamily nm k true)
      | embedFam tp => pure (genv.addCtor nm tp)
      | _ => fail ("Expected kind or type: " ++ repr e)
    | "define" => do
      nm ← symbol;
      val ← expr Any (Environment.new genv);
      let cmd := Command.define nm val;
      rparen;
      pure $ (genv.addCommand cmd).insert nm (EnvDef.defDecl val)
    | "program" => do
      nm ← symbol;
      args ← list (parens (Prod.mk <$> symbol <*> familyName genv));
      ret ← familyName genv;
      let genv' := genv.addProgramDecl nm args ret;
      d ← code CodeReq.anyCode (Environment.code genv' args);
      rparen;
      let cmd := Command.program nm args ret d;
      pure $ genv'.addCommand cmd
    | "check" => do
      cmd ← Command.check <$> checkValue (Environment.new genv);
      rparen;
      pure (genv.addCommand cmd)
    | _ => do
      fail ("Unexpected command " ++ h)
  -- plf files sometimes contain extra rparens that are ignored
  else if c = ')' then do
    skip $> genv
  else
    fail "Expected start of command"

partial
def plf : GlobalEnvironment → Parser GlobalEnvironment
| env => do
  b ← hasMore;
  if b then
    command env >>= plf
  else
    pure env

def processFile (env:GlobalEnvironment) (path:String) : IO GlobalEnvironment := do
  contents ← IO.readTextFile path;
    match (plf env).run path contents with
    | Except.ok env' =>
      pure env'
    | Except.error e =>
      throw (IO.userError ("LFSC Error: " ++ repr e ++ "\n"))

end lfsc

def main (args:List String) : IO Unit := do
  let env1 := lfsc.GlobalEnvironment.init;
  env ← args.foldlM lfsc.processFile env1;
  env.commands.reverse.forM (λc => IO.Prim.putStr (repr c ++ "\n"))
