/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.Pade
import JSP870.Erdos1050.Residue
import JSP870.Erdos1050.QLagrange

/-!
# Denominator integrality (Borwein Lemma 2) + the q-Lagrange identity

Part of the now-complete, **axiom-clean** proof of Erdős #1050 (`#print axioms erdos_1050 =
[propext, Classical.choice, Quot.sound]`). This file machine-checks **Borwein Lemma 2** (integrality of
the q-Padé denominator `pₙ`) and pins the approximant to the actual Padé denominator `pVal`: the
coefficient `β^{2n}·Wₙ·pVal n` is the PROVEN integer `Bden n` (`Bden_cast`), built from `pInt`
(Lemma 2 via the Cauchy q-binomial theorem `qBin_cauchy`) and the 3-power / 2-power clearings of `Wₙ`.
It also derives `qLag_thm` (the q-Lagrange identity at `q = 2`) from `qLagrange` (`QLagrange.lean`).

The downstream chain `borwein_integrality → irrational_zB → erdos_1050` lives in `Lemma3.lean` (after
the elementary Lemma-3 machinery, which is what made the whole proof axiom-clean).
-/

namespace JSP870.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The `3^n`-cleared `c`-product `∏_{k=1}^n (3 − 8·2^k) ∈ ℤ` (clears `∏(1 − c·q^k)`, `c = 8/3`). -/
def CPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, (3 - 8 * 2 ^ k)

/-- The integer `q`-product `∏_{k=⌈n/2⌉}^n (1 − 2^k) ∈ ℤ` (equals `∏(1 − q^k)`, `q = 2`). -/
def QPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - 2 ^ k)

/-- The cleared **integer denominator** `β^{2n}·Wₙ·pₙ`, assembled from the factorial, the cleared
products, and the cleared Padé denominator `pInt`. -/
def Bden (n : ℕ) : ℤ :=
  3 * (Nat.factorial (n - 2)) * CPint n * QPint n * pInt n

/-- `(CPint n : ℝ) = 3^n · ∏_{k=1}^n (1 − c·q^k)`. -/
lemma CPint_cast (n : ℕ) :
    (CPint n : ℝ) = 3 ^ n * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k) := by
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  rw [CPint]
  push_cast
  rw [show (3 : ℝ) ^ n = ∏ _k ∈ Finset.Icc 1 n, (3 : ℝ) from by rw [Finset.prod_const, hcard],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [cB, qB]; ring

/-- `(QPint n : ℝ) = ∏_{k=⌈n/2⌉}^n (1 − q^k)`. -/
lemma QPint_cast (n : ℕ) :
    (QPint n : ℝ) = ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k) := by
  rw [QPint]
  push_cast
  apply Finset.prod_congr rfl
  intro k _
  simp only [qB]

/-- **Denominator integrality (Borwein Lemma 2, USED).** `(Bden n : ℝ) = β^{2n}·Wₙ·pVal n`, so the
Padé denominator coefficient is a machine-checked integer. -/
lemma Bden_cast {n : ℕ} (hn : 1 ≤ n) :
    (Bden n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n * pVal n := by
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ (2 * n) := by simp [βB]
  have key : (3 : ℝ) * 3 ^ n * 3 ^ (n - 1) = 3 ^ (2 * n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show 2 * (m + 1) = (m + 1) + m + 1 from by ring,
      pow_add, pow_add, pow_one]
    ring
  rw [Bden]
  push_cast
  rw [CPint_cast, QPint_cast, pInt_cast, Wterm, hb]
  rw [← key]
  ring

/-- **The q-Lagrange identity (Piece IIIb), now a THEOREM.** `∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`
for `i < n`. This was the first clause of the former `residue_open` axiom; it is now discharged by
`qLagrange` (auto-formalized by Aristotle, ported + verified axiom-clean in `QLagrange.lean`),
specialized to `q = qB = 2`. It discharges `pFirst_eq_pVal`'s hypothesis, making `Eterm_eq_pVal`
unconditional. -/
theorem qLag_thm {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1) := by
  have h := qLagrange qB one_lt_qB n hn i (by omega)
  simpa only [muW] using h

/- **Numerator integrality (Borwein Lemma 3)** is proved elementarily in `Lemma3.lean`, where the
downstream chain `borwein_integrality → irrational_zB → erdos_1050` is also assembled (it needs the
Lemma-3 machinery). With Lemma 3 machine-checked there, `erdos_1050` is axiom-clean. -/

end JSP870.Erdos1050
