import BrownCs22.Library.Tactics
import BrownCs22.Library.TruthTables
import AutograderLib

/-

# Welcome to the Lean section of HW1!

Some general guidelines, before we get started.

* When you're doing Lean homework assignments, including this one,
  do *not* edit any of the `import` statements above the
  opening comment. This will most likely break our autograder.

* Speaking of: when you submit this on Gradescope, you'll
  upload it to a separate assignment than the PDF with your other
  solutions. That's because we can autograde Lean, but not normal
  math! In the future, we hope to let you upload both files to the
  same assignment. But autograders are tricky and we haven't
  figured it out yet.

* Your goal in this assignment is to replace the `sorry`s in each
  part with completed proofs.

  For example, suppose the original problem looks like this:
-/

theorem example_1 (p : Prop) : p → p → p := by
  sorry
  done

/-

  Notice that, with the `sorry`, `example_1` is highlighted with a
  yellow warning. If you delete the `sorry`, a red error message
  appears at `done`: the proof is not complete!

  A solution is complete if it has no warnings and no error messages:

-/

theorem example_1' (p : Prop) : p → p → p := by
  assume hp1
  assume hp2
  assumption
  done




/-
Let's get started!
-/

variable (p q r s : Prop)

/-

## Problem 1

Fill in the `sorry` in the proof below.
The elimination and introduction rules we talked about in Lecture 4
will be very helpful here!


-/

@[autograded 3]
theorem problem_1 : (p ∧ q) ∧ (r ∧ s) → (p ∧ r) := by
  -- We're trying to prove an implication, so we use the → intro rule:
  -- assume the hypothesis, show the conclusion (we use `assume` to apply this
  -- rule). Every entry in our context needs a name, so we pick `hpqrs` since
  -- this is a *h*ypothesis about variables with those names.
  assume hpqrs
  -- We assumed a conjunction and want to "split it up" into its constituent
  -- propositions. We use conjunction elimination to do this via the `eliminate`
  -- tactic. The names `hpq` and `hrs` will be given to the resulting
  -- "split-out" hypotheses.
  eliminate hpqrs with hpq hrs
  -- We apply conjunction elimination again:
  eliminate hpq with hp hq
  -- And again:
  eliminate hrs with hr hs
  -- Our goal is a conjunction. To prove a conjunction, we need to prove each
  -- side separately: that's the conjunction intro rule. `split_goal` applies
  -- that rule. Now we have two goals: one for the left-hand conjunct and one
  -- for the right-hand one.
  split_goal
  -- We always work on one goal at a time. To "focus" our topmost goal, we use
  -- `{ }`.
  {
    -- Since the goal we want to show is something we've already assumed, the
    -- `assumption` proof rule discharges the goal.
    assumption
  }
  -- We move onto our second goal, which again follows by `assumption`
  {
    assumption
  }
  done



/-

## Problem 2

Consider what the theorem below is saying!
"If the truth of `p` implies the falsity of `q`,
 then `p` and `q` cannot both be true."

Does that seem like a reasonable statement?
What do the truth tables of `p → ¬ q` and `¬ (p ∧ q)` look like?
(You do not need to write an answer, but think about it for a moment.
 Try the `#truth_table` command if you want.)


Again, your task is to fill in the `sorry` below to prove this statement.

-/


@[autograded 3]
theorem problem_2 : (p → ¬ q) → ¬ (p ∧ q) := by
  assume hpnq
  assume hpq  -- This step is a *proof by contradiction*!
              -- To prove `¬ (p ∧ q)`, we assume `p ∧ q` and show a
              -- contradiction.
  eliminate hpq with hp hpq
  have hnq : ¬ q := hpnq hp  -- this step is *modus ponens* (implication elim)
  contradiction  -- at this point, we know both `q` and `¬ q`.
  done


/-
## Problem 3

This one's a little tricky! Let's reason through it in natural language.

We want to prove that, if we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`,
then we know `r ∨ s`.
So suppose that we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`.
Our goal is to show that `r ∨ s` follows.

From that long statement, we know three facts: `p ∨ q`, `p → r`, and `q → s`.
We'll reason by cases on `p ∨ q`.

First, if we know `p`, then we know `r`, because `p → r`.
And if we know `r` then we know `r ∨ s`.

Second, if we know `q`, then we know `s`, because `q → s`.
And if we know `s` then we know `r ∨ s`.

That completes our proof!

Your task: translate this argument to Lean.

-/

@[autograded 4]
theorem problem_3 : ((p ∨ q) ∧ (p → r) ∧ (q → s)) → (r ∨ s) := by
  -- So suppose that we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`:
  assume hand
  -- From that long statement, we know three facts:
  -- `p ∨ q` (that's `hor` below),
  eliminate hand with hor hand2
  -- `p → r` (that's `hpr`), and `q → s` (`hqs`)
  eliminate hand2 with hpr hqs
  -- We'll reason by cases on `p ∨ q` ("cases" = or elim!)
  eliminate hor with hp hq
  -- First, if we know `p` (this is case 1 = goal 1)
  { left -- if we know `r` then we know `r ∨ s` (this is the left or intro rule)
    have hr : r := hpr hp -- because `p → r` (modus ponens, since we know `p`)
    assumption }
  -- (The reasoning for the second case is similar)
  { right
    have hs : s := hqs hq
    assumption }
  done
