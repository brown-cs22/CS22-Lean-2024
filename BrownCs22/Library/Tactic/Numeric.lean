import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

-- # Induction
syntax (name := ensureUniversalTac) "ind_ensure_univ" : tactic
@[tactic ensureUniversalTac] def ensureGoalUniversal : Tactic :=
  λ _ => withMainContext do
  if let .forallE _ tp _ _ := (← getMainTarget) then
    if (← isDefEq tp (Expr.const `Nat [])) then
      return
  throwError ("The goal is not universally quantified over a natural number, "
              ++ "so natural-number induction cannot be applied.")

@[elab_as_elim]
lemma Nat.induction {P : ℕ → Prop} : P 0 → (∀ n, P n → P (n+1)) → (∀ n, P n) :=
  Nat.rec
macro "basic_induction" : tactic =>
  `(tactic| (ind_ensure_univ; apply Nat.induction))

macro "strong_induction" : tactic =>
  `(tactic| (ind_ensure_univ;
             intro n;
             refine Nat.strong_induction_on n ?_;
             clear n))

macro "induction_from_starting_point" : tactic =>
  `(tactic| (ind_ensure_univ; apply Nat.le_induction))


-- # Computation
macro "linarith" : tactic => `(tactic| first | ring1 | linarith)

section
open Lean.Meta Qq Lean.Elab Term
open Lean.Parser.Tactic Mathlib.Meta.NormNum

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹`
and `^` over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general
algebraic types, and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and
`A ≤ B`, where `A` and `B` are numerical expressions.
-/
elab (name := numbers) "numbers" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)
end
