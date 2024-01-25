import Lean
/-
NOTE: The custom `by` environment is *not* being used for CS 22 Spring 2024. Do
not import this file!
-/
open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

-- # By/Done
open Lean.Syntax in
partial def getLastNode : Syntax → Option Syntax := λ stx => match stx with
  | node SourceInfo.none kind args =>
    dbg_trace stx
    dbg_trace ("args: " ++ toString args)
    args.findSomeRev? getLastNode
  | stx@(node ..) =>
    dbg_trace "here"
    some stx
  | stx@(ident info ..) =>
    dbg_trace "got here"
    info.getPos?.map fun _ => stx
  | stx@(atom ..) => dbg_trace "stx"
      stx
  | _ => none

-- TODO: set `editor.lightbulb.visible: false` in Codespace VS Code config
-- TODO: disable `linter.unusedVariables`
open Lean.Elab Lean.Elab.Term in
-- FIXME: why does `by` with no tactics fail to show goal/error msg?
-- Is it because we're using `term_elab` instead of `builtin_term_elab`?
@[term_elab byTactic] def elabByTacticMandatingDone : TermElab :=
  λ stx expectedType? => do
    -- Ensure the tactic block contains `done`
    -- TODO: can we ensure that it *ends* with `done`?
    -- FIXME: we need to recurse through sub-syntax or something -- this fails
    -- with an opening `{ }`
    match stx.find? (· == (← `(tactic| done))) with
    | none =>
      -- Show error at the end of the tactic block
      let errStx := stx.getTailWithPos.getD stx
      throwErrorAt errStx "Missing `done` at end of tactic block"
    | some doneStx =>
      -- if let some tlStx := getLastNode stx then
      --   -- FIXME: this is an absolutely horrendous way to test for this
      --   if (doneStx.getArg 0 |>.getPos?) != tlStx.getPos? then
      --     throwErrorAt doneStx "`done` should appear only at the end of the proof"

      throwUnsupportedSyntax
    -- This approach does not work
    -- match stx with
    -- | `(by $ts:tactic*) =>
    --   let tdone ← `(tactic| done)
    --   logInfo m!"{stx.find? (· == tdone)}"
    --   if let some firstDone := ts.getElems.findIdx? (· == tdone) then
    --     if firstDone != ts.getElems.size - 1 then
    --       throwErrorAt ts.getElems[firstDone]!
    --         "`done` should only appear at the end of a tactic block"
    --   else
    --     throwError "Missing `done` at end of tactic block"

      -- Defer to standard elaborator
      -- elabByTactic stx expectedType?
      -- throwUnsupportedSyntax
    -- | _ => throwUnsupportedSyntax
-- This is a ridiculous workaround
syntax (name := emptyByWorkaround) "by" : term
open Lean.Elab Lean.Elab.Term in
@[term_elab emptyByWorkaround] def elabEmptyBy : TermElab := λ stx etp? => do
  throwError "Missing `done` at end of tactic block"

-- @[macro Lean.Parser.Tactic.rwSeq] def rwDisabler : Macro
-- | `(Lean.Parser.Tactic.rwRuleSeq| [$rs,*]%$rbrak) =>
--   -- `(tactic| rfl)
--   `(tactic| fail "`rw` has been disabled. Use `rewrite` instead.")
-- | _ =>
--   Macro.throwUnsupported
