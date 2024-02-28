import BrownCs22.Library.Tactics
open Dvd
/-

# Induction in Lean

There are tactics corresponding to the induction principles we saw in class.
Think about it: how many goals should each induction principle produce?
What hypotheses do we have in each goal?



* `basic_induction` is the normal, one-step, starting-from-0 induction:

-/

example (P : ℕ → Prop) : ∀ n, P n := by
  basic_induction
  { sorry } -- show `P 0`
  { fix n
    assume h_ind
    sorry } -- assuming `P n`, show `P (n + 1)`



/-

* `induction_from_starting_point`: again, as the name implies, this lets
  us start a normal induction proof from a value besides 0.

-/

example (P : ℕ → Prop) : ∀ n ≥ 4, P n := by
  induction_from_starting_point
  { sorry } -- prove `P 4`
  { fix n
    assume hn4
    assume h_ind
    sorry } -- assuming `4 ≤ n` and `P n`, show `P (n + 1)`




/-

Here's an example we did in class, typed into Lean!

-/

example : ∀ n ≥ 5, 2^n > n^2 := by
  induction_from_starting_point
  { numbers }
  { fix n
    assume hn5
    assume ih
    have hle : 2*n + 1 ≤ n^2
    { nlinarith }
    calc (n+1)^2 = n^2 + 2*n + 1 := by linarith
               _ ≤ n^2 + n^2     := by linarith
               _ < 2^n + 2^n     := by linarith
               _ = 2^n * 2       := by linarith
               _ = 2 ^ (n + 1)   := by rw [pow_add, pow_one]
  }










/-

* `strong_induction` is, as the name implies, an induction principle
  that lets us assume `P` holds of *all* smaller numbers.
  Why is there no base case here?

-/

example (P : ℕ → Prop) : ∀ n, P n := by
  strong_induction
  fix n
  assume h_ind
  sorry -- assuming `∀ (m : ℕ), m < n → P m`, show `P n`


/-

There's no base case because if we can prove the strong induction step
for every `n`, it must hold for `0`, which implies `P 0`:

-/

example (P : ℕ → Prop) (hn : ∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n) :
    P 0 := by
  have hn0 : (∀ (m : ℕ), (m < 0 → P m)) → P 0 := hn 0
  apply hn0
  fix m
  assume hm
  contradiction



/-

For a longer example (that we won't talk through in class):
here's another proof we did on the slides:
any value `n ≥ 8` can be written as a combo of coins worth 3 and 5.

This proof uses the tactic `omega`, which will prove "obvious things"
about the natural numbers, a lot like `linarith`.

-/

example : ∀ n ≥ 8, ∃ a b : ℕ, 3*a + 5*b = n := by
  strong_induction
  fix n
  assume hall
  assume hn
  have hor : n = 8 ∨ n = 9 ∨ n = 10 ∨ n ≥ 11 := by omega
  eliminate hor with h8 hor
  { existsi 1
    existsi 1
    rewrite h8
    numbers }
  { eliminate hor with h9 hor
    { existsi 3
      existsi 0
      rewrite h9
      numbers }
    { eliminate hor with h10 hor
      { existsi 0
        existsi 2
        rewrite h10
        numbers }
      { have h1 : n - 3 < n := by omega
        have h2 : n - 3 ≥ 8 := by omega
        have hex : ∃ a b, 3*a + 5*b = n - 3 := hall _ h1 h2
        eliminate hex with a hb
        eliminate hb with b hab
        existsi a + 1
        existsi b
        omega } } }
