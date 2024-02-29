import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import Mathlib.Tactic.Polyrith
import AutograderLib

open Dvd

/-

# Welcome to the Lean section of HW5!

Today we'll explore *induction* in Lean.

The tactics we introduced in class (in Lecture 15) were
`basic_induction`, `induction_from_starting_point`, and `strong_induction`.
Each of these applied when the goal had the shape `∀ n : ℕ, ...`,
which matches our normal induction pattern: it's a technique for proving facts
about all natural numbers (or perhaps all natural numbers starting from some bound).

Take a look at the descriptions of these tactics in the CS22 Lean docs
before you start on these problems!

-/


/-

## Problem 1

Here we prove a basic inequality about natural numbers.
`linarith` will help you in the inductive step of your proof, but only so much.
You're going to need to guide it. A good way to do this is with a `calc` block,
exactly like we saw in Lecture 15. In a `calc` block you provide
intermediate steps in a chain of equalities and inequalities.
Here's an example:

-/

example : ∀ (t : ℚ), t ≥ 10 → t ^ 2 - 3 * t - 17 ≥ 5 := by
  fix t
  assume ht
  calc
    t ^ 2 - 3 * t - 17 = t * t - 3 * t - 17 := by linarith
    _ ≥ 10 * t - 3 * t - 17 := by nlinarith
    _ = 7 * t - 17 := by linarith
    _ ≥ 7 * 10 - 17 := by linarith -- (*)
    _ ≥ 5 := by numbers

/-

Note that our `calc` block combines `≥` and `=` to conclude a `≥` statement.

Each line of the `calc` block establishes a relation between the right-hand expression
on the previous line, and the expression on the current line.
For example: at the line marked (*) above, we are proving that
`7 * t - 17 ≥ 7 * 10 - 17`.
Each line (other than the first) must begin with an underscore.
Each line must end with `:= by`, followed by a tactic that will prove that line.

In the example above, before we begin the `calc` block, our goal is
`t ^ 2 - 3 * t - 17 ≥ 5`.
This is why the first expression (on the left hand side of the first line)
is `t ^ 2 - 3 * t - 17`,
and the last expression (on the right hand side of the final line) is `5`.
-/

@[autograded 4]
theorem problem_1 : ∀ n, 2 ^ n ≥ n + 1 := by
  sorry
  done


/-

## Problem 2

No calculation this time, just some logic!
Now we'll prove that every number is either even or odd, phrased in terms of
"divisibility by 2."

-/

@[autograded 4]
theorem problem_2 : ∀ n : ℕ, 2 ∣ n ∨ 2 ∣ n + 1 := by
  sorry
  done
