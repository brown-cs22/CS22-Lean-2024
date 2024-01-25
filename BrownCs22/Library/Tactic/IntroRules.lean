import Lean
import BrownCs22.Library.Tactic.Naming

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

elab (name := split_goal) "split_goal " : tactic => withMainContext do
  let tgt := (← instantiateMVars (← whnfR (← getMainTarget)))
  match tgt.and?, tgt.iff? with
  | .none, .none => throwError "split_goal only applies to ∧ and ↔ goals"
  | _, _ => evalConstructor default

macro "reflexivity" : tactic => `(tactic |rfl)

macro "have " d:haveDecl : tactic =>
  match d.raw.getHead? with
    | none =>
      -- This case should be unreachable, but I'm not confident enough in that
      -- assertion to actually put an `unreachable!` here and risk confusing
      -- students with a server panic in some weird edge case
      `(tactic| fail "Invalid syntax provided to `have`.")
    | some nmStx =>
      let nm := nmStx.getId
      if nm.isAnonymous then
        let errStr := "Your `have` declaration is missing a name. Make sure to "
            ++ "specify a name for your new hypothesis before the colon."
        `(tactic| fail $(Syntax.mkStrLit errStr))
      else if !(isValidHypName nm.toString) then
        let errStr := "Names of hypotheses should begin with \"h\", but the "
            ++ s!"name \"{nm.toString}\" does not. If you're trying to declare "
            ++ "a piece of data instead, remember that `have` is only for "
            ++ "adding hypotheses to your context, not data."
        `(tactic| fail $(Syntax.mkStrLit errStr))
      else
        `(tactic| refine_lift have $d:haveDecl; ?_)
