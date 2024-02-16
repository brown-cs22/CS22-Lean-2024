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

syntax (name := haveCS22) "have " haveDecl : tactic
@[tactic haveCS22] def elabHaveCS22 : Tactic
| `(haveCS22| have $d:haveDecl) => withMainContext do
  match d.raw.getHead? with
    | none =>
      -- This case should be unreachable, but I'm not confident enough in that
      -- assertion to actually put an `unreachable!` here and risk confusing
      -- students with a server panic in some weird edge case
      throwError "Invalid syntax provided to `have`."
    | some nmStx =>
      let nm := nmStx.getId
      let willShadow := (← getLCtx).decls.any λ
        | none => false
        | some d => !d.isImplementationDetail && d.userName == nm
      if nm.isAnonymous then
        throwError ("Your `have` declaration is missing a name. Make sure to "
                    ++ "specify a name for your new hypothesis before the colon.")
      else if !(isValidHypName nm.toString) then
        throwError ("Names of hypotheses should begin with \"h\", but the "
                      ++ s!"name \"{nm.toString}\" does not. If you're trying to declare "
                      ++ "a piece of data instead, remember that `have` is only for "
                      ++ "adding hypotheses to your context, not data.")
      else if willShadow then
        throwError s!"There is already a hypothesis in your context named \"{nm}\""
      else
          evalTactic (← `(tactic| refine_lift have $d:haveDecl; ?_ ))
            <|> throwError ("Your `have` declaration could not be processed. Most likely, this "
                ++ "means that the expression to the right of the `:=` sign is not syntactically "
                ++ "valid.")
| _ => throwUnsupportedSyntax
