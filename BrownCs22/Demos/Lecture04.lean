import BrownCs22.Library.Tactics

namespace Lecture04

/-

Recall from lecture:
* A *proof state* is a sequence of goals,
  each with an associated list of hypotheses.
* We can manipulate a proof state by applying *proof rules*.
  Proof rules change the goals and/or hypotheses.
* The objective of proving is to apply proof rules
  until there are no remaining goals.

* *introduction rules* tell us how to show goals of certain shapes.
* *elimination rules* tell us how to use hypotheses of certain shapes.

-/

-- let `p, q, r` be propositions.
variable (p q r : Prop)

/-

To start a proof, we write `example :` or `theorem theorem_name :`,
followed by the proposition we are trying to prove,
followed by `:= by`.

What follows after that is a list of proof rules ("tactics").
If we put the cursor at the end of any line, we see the current proof state
after applying that rule.

The lines above the `⊢` symbol are our *context*, i.e. our hypotheses.
The line after the `⊢` is our current goal.

-/

example : p → p := by
  assume hp
  assumption
  done

/-
Here are some useful tactics, corresponding to the intro rules we've seen.

* and introduction: `split_goal`
* or introduction: `left`, `right`
* implication intro: `assume h` (you get to name the new hypothesis)
* iff intro: `split_goal`
* atom: `assumption` (if your goal matches a hypothesis)

* `sorry` proves the goal automatically, no matter what it is.
  This is cheating! :)
-/

example : p → q → p ∧ q := by
  assume hp
  assume hq
  split_goal
  { assumption } -- when we have multiple goals, we sometimes put each subproof in {...}
  { assumption }  -- but this is mainly for style!
  done

example : p → p ∨ q := by
  assume hp
  left
  assumption
  done

-- try it yourself:

example : q → p ∨ q := by
  sorry

example : (p ∧ q) → (p ↔ q) := by
  sorry



/-
*Elimination rules* tell us how we can use hypotheses. To start:

* and elimination: `eliminate h with h1 h2`,
  when `h : p ∧ q` is in the context. Creates new hypotheses
  `h1 : p` and `h2 : q`.
* or elimination: `eliminate h with h1 h2`,
  when `h : p ∨ q` is in the context. Creates new goals,
  one with `h1 : p` in the context and one with `h2 : q` in the context.

-/

example : p ∧ q → q ∧ p := by
  assume hpq
  eliminate hpq with hp hq
  split_goal
  { assumption }
  { assumption }
  done

example : (p ∨ q) → (p ∨ r) ∨ (q ∨ r) := by
  assume hpq
  eliminate hpq with hp hq
  { left
    left
    assumption }
  { right
    left
    assumption }
  done

/-

Using an iff is easy: `eliminate` will turn it into two "imply"s.

-/

example : (p ↔ q) → (p → q) := by
  assume h_iff
  eliminate h_iff with hpq hqp
  assumption
  done


/-

Using an "implies" is a little trickier:
if we know `hpq : p → q` and `hp : p`,
we can "reason forward" by writing `have hq : q := hpq hp`.
This adds a new hypothesis `hq : q` without changing the goal.
This syntax is a little clunky, but we'll use it in a more general setting later.

-/

example : p → (p → q) → q ∧ p := by
  assume hp
  assume hpq
  have hq : q := hpq hp
  split_goal
  { assumption }
  { assumption }
  done


/-

There's an alternative way to use an implication:
if we know `hpq : p → q`, and our goal is to prove `q`,
then `apply hpq` will change the goal to `p`.

This is like saying "because `p` implies `q`, in order to show `q`,
it suffices to show `p`."
-/

example : p → (p → q) → q := by
  assume hp
  assume hpq
  apply hpq
  assumption
  done








/- Here's a little logic puzzle.

(h1) Alan likes acorns, and either Betty likes begonias or Carl likes cacti.

(h2) If Betty likes begonias, then Alan doesn’t like acorns.

(h3) If Carl likes cacti, then Betty likes begonias.

Show that these hypotheses are contradictory.

-/

variable (al_ac : Prop) -- the proposition "Alan likes acorns"
variable (betty_beg : Prop) -- the proposition "Betty likes begonias"
variable (carl_cac : Prop) -- the proposition "Carl likes cacti"


theorem these_are_contradictory
    (h1 : al_ac ∧ (betty_beg ∨ carl_cac))
    (h2 : betty_beg → ¬ al_ac)
    (h3 : carl_cac → betty_beg) :
    False := by
  eliminate h1 with h4 h5      -- from h1, we know
                               -- (h4) Alan likes acorns and
                               -- (h5) either Betty likes begonias or Carl likes cacti.
  eliminate h5 with h6 h7      -- let's reason by cases on h5.

  { have h8 : ¬ al_ac := h2 h6 -- First, suppose Betty likes begonias.
                               -- Then, by modus ponens with h2, Alan does not like acorns.
    contradiction }            -- This contradicts h4!

  { have h9 : betty_beg := h3 h7 -- Now suppose Carl likes cacti.
                                 -- By modus ponens with h3, Betty likes begonias.
    have h10 : ¬ al_ac := h2 h9  -- But now again by modus ponens with h2, Alan does not like acorns.
    contradiction }              -- Another contradiction!
                                 -- We've finished all our goals.


/-

You've just seen the missing connective.
We skipped rules for negation introduction and elimination before.

This example just showed how to *use* a negation:
if we have hypotheses `hp : p` and `hnp : ¬ p`, then
`contradiction` will prove any goal.

How to introduce a negation? This uses a technique called
"proof by contradiction", which we'll motivate in class soon.

-/




end Lecture04
