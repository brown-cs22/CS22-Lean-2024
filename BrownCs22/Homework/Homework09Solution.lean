import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import AutograderLib

/-

# Strong Induction (Mindbender)

Way back in HW5, you got some practice using the tactic `basic_induction`.
Now get ready for `strong_induction`! This is an
alternative induction tactic that can be used on induction proofs where using
`basic_induction` would be awkward and confusing.

Informally: using basic induction, in our inductive step, we get to assume `P(n)`
and need to prove `P(n+1)`. Using strong induction, We get to assume more in the
inductive step: we assume `P(0)`, `P(1)`, ..., `P(n)`, and need to prove `P(n+1)`.
Generically, we can say that our induction hypothesis is `∀ k, k ≤ n → P(k)`:
"`P` holds for all `k` between 0 and `n` inclusive."

A slight variant of this lets us get rid of the base case -- how useful!
We assume `∀ k, k < n → P(k)` and prove `P(n)`.
We talked about this briefly in class way back when, on Feb 22.



Now in Lean!

Recall that `basic_induction` transforms a goal of `∀ (x : ℕ), P(x)` into two new
goals: `P(0)` and `∀ (x : ℕ), P(x) → P(x+1)`.

On the other hand, `strong_induction` only creates one new goal -- it uses the
variant version of strong induction. However, the transformed goal can look quite
confusing in Lean, so we're going to walk through it step by step.

-/

variable (P : Nat → Prop)

example : ∀ (x : ℕ), P x := by
  strong_induction
  sorry

/-

The example above shows that the `strong_induction` tactic replaces our goal with:

`∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n`

Seeing this, it's natural to ask two questions:
1. Why would proving this let us prove our goal?
2. What does this even mean?

To try to answer these questions, let's isolate the middle part of that expression:

`(∀ (m : ℕ), m < n → P m)`

In English, we can read that proposition as, "`P` is satisfied for all natural numbers
less than `n`." Let's extract this proposition into a named predicate `SatisfiedBelow`,
to hopefully make things clearer.

`SatisfiedBelow n ↔ (∀ (m : ℕ), m < n → P m)`

So `SatisfiedBelow n` is true iff `P` is satisfied for all natural numbers below `n`.

Using that named predicate, we can rewrite the goal given to us by `strong_induction`:

`∀ (n : ℕ), SatisfiedBelow n → P n`

In this form, it's a lot easier to recognize the goal as the definition of strong
induction we discussed in class. This is saying that for all `n`, if `P` is true
for all natural numbers below `n`, then `P` is true for `n` as well. And since
`SatisfiedBelow n` is *vacuously true* when `n = 0`, proving this goal will
automatically prove `P 0`, and therefore also `P 1`, and `P 2`, and so on.



# The Problem

We're going to use the `strong_induction` tactic to prove something we discussed
in class - that all natural numbers 8 or larger can be made using coins of value
3 and 5.

Here's the predicate `P` we'll be working with:

-/

def from_three_five (n : ℕ) : Prop :=
  ∃ (x y : ℕ), n = 3 * x + 5 * y

/-

You'll need these three lemmas - they shouldn't require more than a few lines each to prove.

-/

@[autograded 0.25]
lemma ftf8 : from_three_five 8 := by
  existsi 1
  existsi 1
  numbers
  done

@[autograded 0.25]
lemma ftf9 : from_three_five 9 := by
  existsi 3
  existsi 0
  numbers
  done

@[autograded 0.25]
lemma ftf10 : from_three_five 10 := by
  existsi 0
  existsi 2
  numbers
  done

/-

Now for the tricky parts. This next lemma is a proof that if `n` is between 8 and
10, inclusive, then it can be made from 3 and 5. This follows from the three lemmas
above, but it will be useful to get it into this form. Your main tool in this proof
will be the Mathlib lemma `lt_or_le`, which is a proof that for any natural numbers
`x` and `y`, either `x < y`, or `y ≤ x`. (It actually works for more than just natural
numbers, but we won't go into that.)

You can introduce the lemmas above into your context using `have`:

  `have hn10 : from_three_five 10 := ftf10`

will create a new hypothesis `hn10 : from_three_five 10` in your context.


-/

#check lt_or_le

@[autograded 1]
lemma ftf_of_ge_8_le_10 (n : ℕ) : 8 ≤ n ∧ n ≤ 10 → from_three_five n := by
  assume h
  eliminate (lt_or_le n 9) with hn9 h9n
  {
    have hn8 : n = 8 := by linarith
    rewrite hn8
    have hftf8 : from_three_five 8 := ftf8
    assumption
  }
  {
    eliminate (lt_or_le n 10) with hn10 h10n
    {
      have hn : n = 9 := by linarith
      rewrite hn
      have hftf9 : from_three_five 9 := ftf9
      assumption
    }
    {
      have hn : n = 10 := by linarith
      rewrite hn
      have hftf10 : from_three_five 10 := ftf10
      assumption
    }
  }

/-

Two more helper lemmas, and then we finish this once and for all. These two are
*almost* the same - the first says that if `n` can be made from 3 and 5, so can `n+3`.
The second says that if `n-3` can be made from 3 and 5, so can `n`. Consider:
why aren't these *exactly* equivalent? And why does the second lemma require the
extra hypothesis `3 ≤ n`?

The tactic `omega` may come in handy here and below -- it's just like `linarith`,
but specifically for the natural numbers, and handles natural number subtraction
a lot better.

-/

@[autograded 0.5]
lemma ftf_add_3_of_ftf_self (n : ℕ) :
    from_three_five n → from_three_five (n+3) := by
  assume hftfn
  eliminate hftfn with x hx
  eliminate hx with y hxy
  existsi (x + 1)
  existsi y
  linarith
  done

@[autograded 0.5]
lemma ftf_of_ftf_sub_3 (n : ℕ) :
    3 ≤ n → from_three_five (n-3) → from_three_five n := by
  assume h_3_le_n hftf
  have hn : n = (n-3) + 3 := by omega
  rewrite hn
  apply ftf_add_3_of_ftf_self
  assumption
  done

/-
Again, `linarith` and `omega` will be your friends here!
-/

@[autograded 1]
lemma all_from_three_five : ∀ (n : ℕ), 8 ≤ n → from_three_five n := by
  strong_induction
  fix n
  assume hind h
  eliminate (lt_or_le n 11) with hn11 h11n
  {
    have hbd := ftf_of_ge_8_le_10 n
    have hn10 : n ≤ 10 := by linarith
    have hand : 8 ≤ n ∧ n ≤ 10
    { constructor
      assumption
      assumption }
    have hftf : from_three_five n := hbd hand
    assumption
  }
  {
    apply ftf_of_ftf_sub_3
    { linarith }
    { apply hind
      { omega }
      { omega } }
  }
