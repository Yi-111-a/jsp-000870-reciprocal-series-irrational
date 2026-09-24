/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.Lemma3

/-!
# Erdős Problem #1050 — is `∑_{n ≥ 1} 1/(2ⁿ − 3)` irrational?

## The statement

> The real number `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational.

exactly as posed on erdosproblems.com (`Is ∑_{n=1}^∞ 1/(2ⁿ − 3) irrational?`, answer: yes).

Formalised as `erdos_1050 : Irrational (∑' n : ℕ, 1/(2^(n+1) − 3))`. Lean's `∑' n : ℕ` ranges over
`n ≥ 0`, so the source's `n ≥ 1` sum is encoded by the standard reindex `n ↦ n + 1` (the tsum's
`n = 0` summand is the source's first term, `1/(2¹ − 3)`). That `(n+1)` shift is the *only* thing to
reconcile against the source, and it is transparent.

**This file is the audit surface.** To check that this repository proves the *right thing*, read only
this file: the theorem `erdos_1050` is the entire trusted statement. Everything else
(`Basic.lean`, `Criterion.lean`, `Approximants.lean`, `Lemma3.lean`, …) is the proof engine.

## Provenance

* **Problem source.** P. Erdős & R. Graham, relayed at <https://www.erdosproblems.com/1050>
  ("Is `∑_{n=1}^∞ 1/(2ⁿ − 3)` irrational?", answer yes).
* **Resolving theorem.** P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory
  **37** (1991) 253–259 (and the cleaner *On the irrationality of certain series*, Math. Proc. Camb.
  Phil. Soc. **112** (1992) 141–146), specialized to `q = 2, r = −3`.

## Faithfulness notes

* **Indexing.** The series runs over `n ≥ 1` (the source's `∑_{n=1}^∞`). In Lean it is the tsum
  `∑' n : ℕ, 1/(2^(n+1) − 3)`, whose `n = 0` summand `1/(2¹ − 3) = −1` is the source's first term.
* **Well-definedness.** `2ⁿ − 3` is never `0` (`2ⁿ = 3` has no solution), so every term `1/(2ⁿ − 3)`
  is a genuine real.
* **Reduction (proved, not asserted).** The proof engine works with the positive-denominator tail
  `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)` (see `Basic.lean`); the headline reduces the literal series to it by
  `(∑_{n ≥ 1} 1/(2ⁿ − 3)) = -1 + S` — the single low term `1/(2¹−3) = -1` is rational, and
  irrationality is invariant under adding a rational, so `erdos_1050 ↔ erdos_1050_irrational`. This
  equivalence is `Sliteral_eq`, proved below.
* **Axiom footprint.** `#print axioms erdos_1050` should end at
  `[propext, Classical.choice, Quot.sound]` (kernel-pure; no `native_decide`, no custom axioms).
-/

namespace JSP870.Erdos1050

open scoped BigOperators

/-- The literal Erdős–Graham series `∑_{n ≥ 1} 1/(2ⁿ − 3)`, exactly as posed on erdosproblems.com,
encoded over `ℕ` by the reindex `n ↦ n + 1` (so the tsum's `n = 0` summand is the source's first
term, `1/(2¹ − 3)`). -/
noncomputable def Sliteral : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)

/-- The literal series is the positive-denominator tail `S` shifted by the one rational low term:
`∑_{n ≥ 1} 1/(2ⁿ − 3) = -1 + S`, since its first term is `1/(2¹−3) = -1`. -/
theorem Sliteral_eq : Sliteral = -1 + S := by
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1)
    exact h.mp (by simpa using S_summable)
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1 hsummable
  have hfin : (∑ i ∈ Finset.range 1, (1 : ℝ) / ((2 : ℝ) ^ (i + 1) - 3)) = -1 := by
    simp only [Finset.sum_range_one]; norm_num
  rw [hfin] at hsplit
  simp only [Sliteral, S]
  rw [← hsplit]

/-- **Erdős Problem #1050.** The series `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational, exactly as posed on
erdosproblems.com and encoded over `ℕ` by the reindex `n ↦ n + 1`. This is the trusted headline; its
statement is character-for-character the one published to `formal-conjectures`. -/
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  show Irrational Sliteral
  rw [Sliteral_eq, show (-1 : ℝ) + S = S + ((-1 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff]
  exact erdos_1050_S

/-- **Erdős Problem #1050** (positive-denominator tail form, used by the proof engine). -/
theorem erdos_1050_irrational : Irrational S := erdos_1050_S

/-! ### Non-vacuity anchors

Executable evidence that the series computes as intended, so the irrationality claim is not an
artifact of a mis-stated series. (The claim is already self-certifying against the worst failure
mode: mathlib sets a non-summable `tsum` to `0`, and `Irrational 0` is false — so
`erdos_1050` is provable only because the series genuinely converges to a non-rational real,
never vacuously.) -/

/-- Well-definedness: no term is a junk `1/0`, since the denominator `2ⁿ − 3` is never zero. -/
example (n : ℕ) : (2 : ℝ) ^ n - 3 ≠ 0 := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    intro hc; nlinarith

/-- The first terms of the series (`n ≥ 1`) compute to the expected values; the series first goes
positive at `n = 2`. (`n = 0` is *not* in the sum.) -/
example : (1 : ℝ) / (2 ^ 1 - 3) = -1 := by norm_num
example : (1 : ℝ) / (2 ^ 2 - 3) = 1 := by norm_num
example : (1 : ℝ) / (2 ^ 3 - 3) = 1 / 5 := by norm_num

/-- The rational shift connecting the literal series to the engine's tail `S`: the single low term
`n = 1` is exactly `−1` (this is the content of `Sliteral_eq`). -/
example : (∑ i ∈ Finset.range 1, (1 : ℝ) / (2 ^ (i + 1) - 3)) = -1 := by
  simp only [Finset.sum_range_one]; norm_num

end JSP870.Erdos1050
