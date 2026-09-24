/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.Approximants
import JSP870.Erdos1050.QBinom

/-!
# The q-Padé denominator `pₙ` and its integrality (toward Borwein Lemma 2)

`pVal n` is the real value of Borwein's denominator polynomial `pₙ(c,q)` at `c = 8/3`, `q = 2`
(second form, via Gaussian binomials). `pInt n` is the `3^{n-1}`-cleared integer version. The lemma
`pInt_cast` (Borwein Lemma 2, integrality half) says they agree after clearing — so `3^{n-1}·pₙ ∈ ℤ`.

This is a prerequisite for discharging `borwein_integrality` (O1); the remaining piece is the
residue identity (Lemma 1, see `ON-LINE-REQUEST.md`).
-/

namespace JSP870.Erdos1050
open scoped BigOperators

/-- `pₙ(8/3, 2)` (Borwein Lemma 2, second form): the real-valued q-Padé denominator. -/
noncomputable def pVal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-cB) ^ k * qB ^ (k * (k + 3) / 2)
    * qBin qB (n - 1) k * qBin qB (n + k - 1) (n - 1)

/-- The `3^{n-1}`-cleared **integer** q-Padé denominator. -/
def pInt (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-8) ^ k * 3 ^ (n - 1 - k) * 2 ^ (k * (k + 3) / 2)
    * qBin (2 : ℤ) (n - 1) k * qBin (2 : ℤ) (n + k - 1) (n - 1)

/-- `qBin` at the real base `2` is the integer `qBin` cast to `ℝ`. -/
lemma qBin_two_cast (m j : ℕ) : qBin qB m j = ((qBin (2 : ℤ) m j : ℤ) : ℝ) := by
  simpa [qB] using qBin_map (Int.castRingHom ℝ) (2 : ℤ) m j

/-- **Borwein Lemma 2 (integrality of `pₙ`).** `(pInt n : ℝ) = 3^{n-1}·pₙ(8/3,2)`, so the cleared
q-Padé denominator is an integer. -/
lemma pInt_cast (n : ℕ) : (pInt n : ℝ) = 3 ^ (n - 1) * pVal n := by
  rw [pInt, pVal, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hclear : (3 : ℝ) ^ (n - 1) * (-cB) ^ k = (-8) ^ k * 3 ^ (n - 1 - k) := by
    have h3 : (3 : ℝ) ^ (n - 1) = 3 ^ k * 3 ^ (n - 1 - k) := by rw [← pow_add]; congr 1; omega
    have hcB : (-cB : ℝ) = -8 / 3 := by simp only [cB]; ring
    rw [h3, hcB, mul_assoc, mul_comm ((3 : ℝ) ^ (n - 1 - k)) ((-8 / 3 : ℝ) ^ k), ← mul_assoc,
      ← mul_pow, show (3 : ℝ) * (-8 / 3) = -8 by ring]
  rw [qBin_two_cast (n - 1) k, qBin_two_cast (n + k - 1) (n - 1), ← hclear,
    show qB = (2 : ℝ) from rfl]
  ring

end JSP870.Erdos1050
