/-
Obligation extraction through Lean's REAL frontend.

Why not a text splitter, and why not a bare parse loop: see
`safeverifyagent/extract.py`. The short version is that both fail
SILENTLY. A bare `Parser.runParserCategory` loop cannot see `open`, so
scoped notation fails to parse, the tactic block vanishes from the syntax
tree, and a proof reads as having no steps in it with no error raised.
Running the real frontend tracks scope, and errors are COUNTED and
reported rather than swallowed.

Three things this file had to get right, each of which failed loudly the
first time it was run against a toolchain:

* `enableInitializersExecution` must be called before `processHeader`, or
  `importModules` refuses and you get an environment with ZERO modules.
  The failure is not an exception: the parser simply has no token table,
  so `a + b` fails to parse with "unexpected token '+'" and the proof
  body comes back `<missing>`. A file that imports nothing still needs
  this — 631 modules load from the implicit prelude once it is on.
* That makes `main` **unsafe**, because the initializer call is.
* The tactic kind is `Lean.Parser.Tactic.tacticHave__` — TWO trailing
  underscores. `tacticHave_` (one) is not a constant and does not
  compile; `tacticSuffices_` (one) is the right name for the other.
  Guessing either is how you get a parser that finds nothing.

Statements are read as ORIGINAL SOURCE TEXT via `getSubstring?`, not as
the s-expression `toString` gives, because the consumer is an auditor
reading mathematics.

Usage:  lean --run ExtractLemmas.lean <file.lean>
Output: one JSON object on stdout — {"obligations": [...], "errors": n}
-/
import Lean

open Lean Elab Frontend

structure Obligation where
  id        : String
  statement : String
  kind      : String
  deriving Inhabited

/-- Original source text of a syntax node, whitespace-trimmed. -/
def srcText (stx : Syntax) : String :=
  match stx.getSubstring? with
  | some s => s.toString.trimAscii.toString
  | none   => (toString stx).trimAscii.toString

/-- First identifier anywhere under `stx` — the binder name of a `have`
    lives inside `Term.letId`, and of a `suffices` inside a `group`. -/
partial def firstIdent (stx : Syntax) : Option String :=
  if stx.isIdent then some stx.getId.toString
  else stx.getArgs.findSome? firstIdent

/-- The type ascription of a `have`: the term under `Term.typeSpec`. -/
partial def typeSpecOf (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Term.typeSpec then stx.getArgs[1]?
  else stx.getArgs.findSome? typeSpecOf

partial def collect (counter : IO.Ref Nat) (stx : Syntax) :
    IO (Array Obligation) := do
  let mut out := #[]
  let k := stx.getKind
  if k == ``Lean.Parser.Tactic.tacticHave__ then
    let n ← counter.modifyGet fun n => (n, n + 1)
    let id := (stx.getArgs.findSome? fun a =>
      if a.getKind == ``Lean.Parser.Term.letDecl then firstIdent a else none)
      |>.getD s!"_have{n}"
    let stmt := (typeSpecOf stx).map srcText |>.getD (srcText stx)
    out := out.push { id, statement := stmt, kind := "have" }
  else if k == ``Lean.Parser.Tactic.tacticSuffices_ then
    let n ← counter.modifyGet fun n => (n, n + 1)
    -- sufficesDecl: (group `name ":") TYPE (by ...)
    let decl := stx.getArgs.findSome? fun a =>
      if a.getKind == ``Lean.Parser.Term.sufficesDecl then some a else none
    let id := (decl.bind (fun d => d.getArgs[0]?.bind firstIdent))
      |>.getD s!"_suffices{n}"
    let stmt := (decl.bind (·.getArgs[1]?)).map srcText |>.getD (srcText stx)
    out := out.push { id, statement := stmt, kind := "suffices" }
  else if k == ``Lean.Parser.Command.theorem then
    let id := (stx.getArgs.findSome? fun a =>
      if a.getKind == ``Lean.Parser.Command.declId then firstIdent a else none)
      |>.getD "_thm"
    let sig := stx.getArgs.findSome? fun a =>
      if a.getKind == ``Lean.Parser.Command.declSig then some a else none
    let stmt := (sig.bind typeSpecOf).map srcText |>.getD (srcText stx)
    out := out.push { id, statement := stmt, kind := "theorem" }
  for arg in stx.getArgs do
    out := out ++ (← collect counter arg)
  return out

def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => ""
      | '\t' => "\\t"
      | c    => c.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: lean --run ExtractLemmas.lean <file.lean>"
    return 1
  let input ← IO.FS.readFile path
  initSearchPath (← findSysroot)
  -- Must precede processHeader; see the header comment. Without it the
  -- import silently loads nothing and every proof body reads as missing.
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  -- The real frontend, so `open` is in scope and notation resolves.
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  let errors := s.commandState.messages.toList.filter (·.severity == .error)
  let counter ← IO.mkRef 0
  let mut obligations := #[]
  for c in s.commands do
    obligations := obligations ++ (← collect counter c)
  let rows := obligations.toList.map fun o =>
    "{\"id\":\"" ++ jsonEscape o.id ++ "\",\"statement\":\"" ++
      jsonEscape o.statement ++ "\",\"kind\":\"" ++ o.kind ++ "\"}"
  IO.println <|
    "{\"obligations\":[" ++ String.intercalate "," rows ++
    "],\"errors\":" ++ toString errors.length ++ "}"
  return 0
