import Lean
import Std.Tactic.OpenPrivate
import Std.Data.List.Basic
import Mathlib.Lean.Expr.Basic
import BrownCs22.Library.Tactic.Naming

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Lean.TSyntax

namespace Lean.Parser.Tactic

/-!
# Modified version of `evalNames` from `Mathlib.Tactic.Cases`

**Backward compatible implementation of lean 3 `cases` tactic**

This tactic is similar to the `cases` tactic in lean 4 core, but the syntax for
giving names is different:

```
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```

Prefer `cases` or `rcases` when possible, because these tactics promote
structured proofs.
-/
open private getAltNumFields in evalCases ElimApp.evalAlts.go in
def evalNamesCS22 (elimInfo : ElimInfo) (alts : Array ElimApp.Alt)
    (withArg : Syntax) (tgtNms : Array Name)
    (numEqs := 0) (numGeneralized := 0) (toClear : Array FVarId := #[]) :
    TermElabM (Array MVarId × Option MessageData) := do
  let mut names : List Syntax := withArg[1].getArgs |>.toList

  -- msgData will capture any error messages that occur when checking names,
  -- in the following precedence order: arity > shadowing > duplicate > style
  let mut msgData : Option MessageData := none

  -- Prevent shadowing
  let ignoreStx ← `(binderIdent| _)
  let ctx ← getLCtx
  let checkShadowing (nm : Name) : TermElabM (Option MessageData) := (λ _ =>
    let willShadow := ctx.decls.any (λ
    | none => false
    -- Any non-imp-detail that isn't about to be eliminated would be shadowed
    | some d => !d.isImplementationDetail
                  && !(tgtNms.contains nm)
                  && d.userName == nm)
    if willShadow then
      return some (m!"The name \"{nm}\" already exists in your context. "
        ++ "To avoid ambiguity, please choose a different name.")
    else
      return none
  )

  -- Prevent duplicate names
  let (dup?, _, shadowingMsgData?) ← names.foldlM (λ
    | acc@(some _, _, _), _ => pure acc
    | (none, seen, msgData), nameStx => do
      let name := getNameOfIdent' nameStx[0]
      -- TODO: this is really nasty, but we need to get the message out of the
      -- monadic λ in order to mutate msgData
      let msgData := if msgData.isNone then ← checkShadowing name else msgData
      if seen.contains nameStx && nameStx != ignoreStx
      then pure (some nameStx, [], msgData)
      else pure (none, nameStx :: seen, msgData)
  ) (none, [], none)
  if shadowingMsgData?.isSome then
    msgData := shadowingMsgData?
  if let some dup := dup? then
    msgData := some (m!"All names provided to `eliminate` must be unique, but "
                ++ m!"\"{dup}\" appears twice.")

  let mut subgoals := #[]
  -- Track the number of needed names for error messages
  let mut numNeededNames := 0
  -- For each constructor of the inductive type...
  for { name := altName, mvarId := g, .. } in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields (Unhygienic.run `(_))
    numNeededNames := numNeededNames + numFields
    names := names'
    let (fvars, g) ← g.introN numFields
      <| altVarNames.map (getNameOfIdent' ·[0])
    let some (g, subst) ← Cases.unifyEqs? numEqs g {} | pure ()
    let (_, g) ← g.introNP numGeneralized
    let g ← liftM $ toClear.foldlM (·.tryClear) g
    -- ...create a subgoal `g` and populate it with all relevant
    -- values/hypotheses
    for fvar in fvars, stx in altVarNames do
      g.withContext <|
        (subst.apply <| .fvar fvar).addLocalVarInfoForBinderIdent ⟨stx⟩
      -- Allow them to leave arguments unnamed as long as they're explicitly
      -- underscored
      -- TODO: there's got to be a better way to check this
      let hole ← `(_)
      if stx[0] != hole && msgData.isNone then
        msgData := ← g.withContext do
          let nm ← fvar.getUserName
          let tp ← fvar.getType
          match (← inferType tp) with
          | .sort .zero =>
            if ! (isValidHypName nm.toString) then
              return some <| m!"The name \"{nm}\" was given to the hypothesis "
                  ++ m!"\"{tp}\", but names of hypotheses should start with "
                  ++ "\"h\"."
            else
              return none
          | _ =>
            if ! (isValidDataName nm.toString) then
              return some <| m!"The name \"{nm}\" was given to a piece of data "
                      ++ m!"of type {tp}, but names beginning with \"h\" should "
                      ++ m!"be reserved for hypotheses."
            else
              return none
    subgoals := subgoals.push g

  -- Name count check: ensure no excess/daggered names
  let numSuppliedNames := withArg[1].getArgs.size
  if numNeededNames != numSuppliedNames then
    let excessionKind :=
      if numNeededNames > numSuppliedNames
      then "Not enough"
      else "Too many"
    let plur := if numSuppliedNames == 1 then "name was" else "names were"
    -- Will always overwrite msgData since arity errors take precedence
    msgData := some (m!"{excessionKind} names provided to `eliminate`: this "
        ++ m!"elimination rule produces {numNeededNames} named values and/or "
        ++ m!"hypotheses, but {numSuppliedNames} {plur} provided.")

  pure ⟨subgoals, msgData⟩

end Lean.Parser.Tactic

-- TODO: check for implicits
open Meta Elab Tactic Lean.Parser.Tactic in
open private getElimNameInfo in evalCases in
elab (name := eliminate) "eliminate "
  tgts:(casesTarget,+)
  usingArg:((" using " ident)?)
  withArg:((" with " (colGt binderIdent)+)?)
  : tactic => focus do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g ← getMainGoal
  g.withContext do
    -- TODO: there must be a better way to do this
    let tgtStxs := tgts.1.getSepArgs.map (·.getHead?) |>.filterMap id
    let tgtNms := tgtStxs.map (·.getId)

    let elimInfo ← getElimNameInfo usingArg targets (induction := false)
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let ⟨subgoals, msgData⟩ ← evalNamesCS22 elimInfo result.alts withArg tgtNms
                    (numEqs := targets.size) (toClear := targetsNew)
      setGoals subgoals.toList
      -- After we setGoals, throw any deferred errors from evalNamesCS22
      match msgData with
      | none => pure ()
      | some msgData => throwError msgData
