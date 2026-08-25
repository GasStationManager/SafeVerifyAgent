/-
Obligation extraction through Lean's REAL frontend.

Why not a text splitter, and why not a bare parse loop: see
`safeverifyagent/extract.py`. The short version is that both fail
SILENTLY. A bare `Parser.runParserCategory` loop cannot see `open`, so
scoped notation fails to parse, the tactic block vanishes from the syntax
tree, and a proof reads as having no steps in it with no error raised.
Running the real frontend tracks scope, and errors are COUNTED and
reported rather than swallowed.

Usage:  lean --run ExtractLemmas.lean <file.lean>
Output: one JSON object on stdout — {"obligations": [...], "errors": n}

Status: this is the extraction path the design calls for; it has not been
exercised against a Lean toolchain in this repo yet (DESIGN.md §10).
-/
import Lean

open Lean Elab Frontend

structure Obligation where
  id        : String
  statement : String
  kind      : String
  deriving Inhabited

/-- Tactic syntax kinds that introduce a named obligation. -/
def obligationKinds : List Name :=
  [``Lean.Parser.Tactic.tacticHave_, ``Lean.Parser.Tactic.obtain,
   ``Lean.Parser.Tactic.tacticSuffices_]

partial def collect (stx : Syntax) : Array Obligation := Id.run do
  let mut out := #[]
  if obligationKinds.contains stx.getKind then
    -- The binder name is the obligation id; the type ascription is its
    -- statement. Both are read off the syntax tree, never off comments.
    let name := (stx.find? (·.isIdent)).map (·.getId.toString) |>.getD "_"
    out := out.push { id := name, statement := toString stx, kind := "have" }
  for arg in stx.getArgs do
    out := out ++ collect arg
  return out

def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c    => c.toString)

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: lean --run ExtractLemmas.lean <file.lean>"
    return 1
  let input ← IO.FS.readFile path
  initSearchPath (← findSysroot)
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := Command.mkState env messages {}
  -- The real frontend, so `open` is in scope and notation resolves.
  let s ← IO.processCommands inputCtx parserState commandState
  let errors := s.commandState.messages.toList.filter (·.severity == .error)
  let obligations := s.commands.foldl (init := #[]) fun acc c => acc ++ collect c
  let rows := obligations.toList.map fun o =>
    "{\"id\":\"" ++ jsonEscape o.id ++ "\",\"statement\":\"" ++
      jsonEscape o.statement ++ "\",\"kind\":\"" ++ o.kind ++ "\"}"
  IO.println <|
    "{\"obligations\":[" ++ String.intercalate "," rows ++
    "],\"errors\":" ++ toString errors.length ++ "}"
  return 0
