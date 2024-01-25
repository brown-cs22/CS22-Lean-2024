import Lean
import BrownCs22.Library.Tactic.Naming

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

def doSpecificIntro (tacticName : String) (requiresProp : Bool)
  (makeSpecificErrorMsg : Expr → MessageData)
  (generalErrorMsg : MessageData) (nms : TSyntaxArray `ident)
    : TacticM Unit :=  do
  if let #[] := nms then
    throwError m!"The `{tacticName}` tactic takes one or more arguments: e.g., "
        ++ m!"`{tacticName} {if requiresProp then "h" else "n"}`."
  for nmStx in nms do
    let nm := nmStx.getId
    -- It's very important that we re-capture the context at each iteration so
    -- that any variables named on prior iterations show up correctly and not
    -- as metavariable gobbledygook.
    -- Note that we need to capture the context *before* we intro so that we
    -- don't see the newly intro-ed variable when checking for shadowing
    withMainContext do
      let ctx ← getLCtx
      -- This is the last check we perform, but it's the same in both cases, so
      -- make it a lambda for reusability
      let checkShadowing : TacticM Unit := (λ _ =>
          let willShadow := ctx.decls.any (λ
          | none => false
          | some d => !d.isImplementationDetail && d.userName == nm)
          if willShadow && !nm.isAnonymous
          then throwError m!"The name \"{nm}\" already exists in your context. "
              ++ "To avoid ambiguity, please choose a different name for this "
              ++ m!"{if requiresProp then "hypothesis" else "value"}."
          else pure ()
        )
      -- Do the introduction
      let fvarId ← liftMetaTacticAux fun mvarId => do
        try
          let (fvarId, mvarId) ← mvarId.intro nm
          pure (fvarId, [mvarId])
        catch _ =>
          throwError generalErrorMsg

      -- Check that style checks pass (we do this post-hoc so that we can
      -- let intro do any necessary definitional reductions, e.g., noticing
      -- that we can `assume` for a goal of the form `¬ P`, which isn't
      -- syntactically a `∀`)
      withMainContext do
        -- If you forget to put the next line within `wMC`, you'll get RPCErrors
        Lean.Elab.Term.addLocalVarInfo nmStx (mkFVar fvarId)
        let fvtp ← fvarId.getType
        let tgt ← inferType fvtp
        match tgt with
        | .sort .zero =>
          if requiresProp then
            -- Naming error messages should always come last
            -- We allow explicitly anonymous names
            if nm.isAnonymous || isValidHypName nm.toString then
              checkShadowing
            else
              throwError m!"Names of hypotheses should begin with an \"h\", "
              ++ m!"but \"{nm}\" does not."
          else
            throwError (makeSpecificErrorMsg fvtp)
        | _ =>
          if !requiresProp then
            if nm.isAnonymous || isValidDataName nm.toString then
              checkShadowing
            else
              throwError m!"To prevent ambiguity, reserve names beginning with "
                ++ "\"h\" for hypotheses, not data."
          else
            throwError (makeSpecificErrorMsg fvtp)

syntax (name := fixTac) "fix" (ppSpace colGt term:max)* : tactic
@[tactic fixTac] def elabFix : Tactic
| `(tactic| fix $nms:ident*) =>
  doSpecificIntro "fix" false
    (λ tp => m!"\"{tp}\" is a hypothesis, not a value. Use `assume` for "
              ++ "introducing hypotheses into your context.")
    ("Your goal is not a universal quantification, so the `fix` tactic does "
        ++ "not apply.")
    nms
| _ => Elab.throwUnsupportedSyntax

syntax (name := assumeTac) "assume" (ppSpace colGt term:max)* : tactic
@[tactic assumeTac] def elabAssume : Tactic
| `(tactic| assume $nms:ident*) =>
  doSpecificIntro "assume" true
    (λ tp => m!"You are attempting to introduce a bound variable of type {tp}, "
                  ++ "not a hypothesis. Use `fix` for introducing data into "
                  ++ "your context.")
    "Your goal is not an implication, so the `assume` tactic does not apply."
    nms
| _ => Elab.throwUnsupportedSyntax

elab (name := introsOverride) "intros" (ppSpace colGt (ident <|> hole))*
  : tactic => do
  throwError ("`intros` has been disabled. Use `fix` to introduce data or "
    ++ "`assume` to introduce hypotheses.")
elab (name := introOverride) "intro" notFollowedBy("|")
                                     (ppSpace colGt term:max)* : tactic => do
  throwError ("`intro` has been disabled. Use `fix` to introduce data or "
      ++ "`assume` to introduce hypotheses.")
