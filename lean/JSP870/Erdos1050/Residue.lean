/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.Pade

/-!
# Elementary (contour-free) proof of Borwein's residue identity — Piece II: the geometric collapse

The previous laps reduced Erdős #1050 to the single axiom `borwein_integrality`, whose only deep
component is Borwein's Lemma 1 (the residue identity). This file begins a **fully elementary** proof
of that identity (no contour integral); see `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md` for the full
strategy. The crux is the **collapse of the auxiliary series**

  `T_i := ∑_{h≥1} q^{-i·h} / (1 − c·q^h)  =  c^i · z  +  R_i`,    `R_i ∈ ℚ`,

which is what the contour integral was hiding. This is proved here by the per-term identity

  `q^{-i·h}/(1−c·q^h) = q^{-i·h} + c · q^{-(i-1)·h}/(1−c·q^h)`

(`key_term` below), a geometric series, and induction on `i`. Indexing matches `zB`: we sum over
`j : ℕ` with `h = j + 1`.
-/

namespace JSP870.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The rational correction `R_i = ∑_{l=1}^{i} c^{i-l}/(q^l − 1)`, via the recurrence
`R_{i+1} = 1/(q^{i+1} − 1) + c·R_i`, `R_0 = 0`. -/
noncomputable def Rrat : ℕ → ℝ
  | 0 => 0
  | (i + 1) => 1 / (qB ^ (i + 1) - 1) + cB * Rrat i

/-- The auxiliary series `T_i = ∑_{h≥1} q^{-i·h}·(1 − c·q^h)⁻¹` (with `h = j + 1`).
All exponents are non-positive, so we use `(qB^…)⁻¹` (natural power) rather than `zpow`. -/
noncomputable def Tser (i : ℕ) : ℝ :=
  ∑' j : ℕ, (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹

/-- The per-term collapse identity. With `P = q^h` (`P ≠ 0`, `1 − c·P ≠ 0`):
`(P^{i+1})⁻¹·(1−cP)⁻¹ = (P^{i+1})⁻¹ + c·(P^i)⁻¹·(1−cP)⁻¹`. -/
lemma key_term (P : ℝ) (i : ℕ) (hP : P ≠ 0) (hcP : 1 - cB * P ≠ 0) :
    (P ^ (i + 1))⁻¹ * (1 - cB * P)⁻¹
      = (P ^ (i + 1))⁻¹ + cB * (P ^ i)⁻¹ * (1 - cB * P)⁻¹ := by
  have hPi : P ^ i ≠ 0 := pow_ne_zero i hP
  have hPi1 : P ^ (i + 1) ≠ 0 := pow_ne_zero (i + 1) hP
  field_simp
  ring

/-- `q^{j+1} ≠ 0`. -/
private lemma qpow_ne (j : ℕ) : qB ^ (j + 1) ≠ 0 := pow_ne_zero _ qB_ne

/-- Per-term absolute bound `|q^{-i(j+1)}·u_{j+1}| ≤ (1/2)^{j+1}`. -/
lemma Tterm_abs_le (i j : ℕ) :
    |(qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹| ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  rw [abs_mul]
  have h1 : |(qB ^ (i * (j + 1)))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
  have h2 : |(1 - cB * qB ^ (j + 1))⁻¹| ≤ qB ^ (-((j : ℤ) + 1)) := by
    have h := inv_cqpow_le (a := (j : ℤ) + 1) (by omega)
    have he : qB ^ ((j : ℤ) + 1) = qB ^ (j + 1) := by
      rw [← zpow_natCast qB (j + 1)]; norm_num
    rwa [he] at h
  have h3 : qB ^ (-((j : ℤ) + 1)) = (1 / 2 : ℝ) ^ (j + 1) := by
    rw [show (-((j : ℤ) + 1)) = -(((j + 1 : ℕ) : ℤ)) by push_cast; ring, qB_neg_zpow]
  calc |(qB ^ (i * (j + 1)))⁻¹| * |(1 - cB * qB ^ (j + 1))⁻¹|
      ≤ 1 * qB ^ (-((j : ℤ) + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (1 / 2 : ℝ) ^ (j + 1) := by rw [one_mul, h3]

/-- `T_i` is summable (dominated by the geometric `(1/2)^{j+1}`). -/
lemma Tser_summable (i : ℕ) :
    Summable (fun j : ℕ => (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j; rw [Real.norm_eq_abs]; exact Tterm_abs_le i j

/-- `T_0 = z`. -/
lemma Tser_zero : Tser 0 = zB := by
  unfold Tser zB
  apply tsum_congr
  intro j
  simp

/-- The geometric piece `∑_{j} q^{-(i+1)(j+1)} = 1/(q^{i+1} − 1)`. -/
lemma geom_piece (i : ℕ) :
    ∑' j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = 1 / (qB ^ (i + 1) - 1) := by
  set r : ℝ := (qB ^ (i + 1))⁻¹ with hr
  have hrpos : 0 < r := by rw [hr]; exact inv_pos.mpr (pow_pos qB_pos _)
  have hqgt : (1 : ℝ) < qB ^ (i + 1) := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ (i + 1) := pow_le_pow_right₀ (le_of_lt one_lt_qB) (by omega)
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hqgt
  have hconv : ∀ j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = r * r ^ j := by
    intro j; rw [hr, ← pow_succ', inv_pow, ← pow_mul]
  rw [tsum_congr hconv, tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hrpos) hr1, hr]
  have hx1 : (1 : ℝ) - (qB ^ (i + 1))⁻¹ ≠ 0 := by
    have : (qB ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqgt
    linarith
  have hx0 : (qB : ℝ) ^ (i + 1) ≠ 0 := ne_of_gt (pow_pos qB_pos _)
  have hx2 : (qB : ℝ) ^ (i + 1) - 1 ≠ 0 := by linarith [hqgt]
  field_simp

/-- The geometric piece is summable. -/
lemma geom_summable (i : ℕ) : Summable (fun j : ℕ => (qB ^ ((i + 1) * (j + 1)))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    have h1 : (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ :=
      inv_anti₀ (pow_pos qB_pos _)
        (pow_le_pow_right₀ (le_of_lt one_lt_qB) (by rw [Nat.succ_mul]; omega))
    calc (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ := h1
      _ = (1 / 2 : ℝ) ^ (j + 1) := by
          rw [show (1 / 2 : ℝ) = qB⁻¹ by norm_num [qB], inv_pow]

/-- **The collapse recurrence**: `T_{i+1} = 1/(q^{i+1} − 1) + c·T_i`. -/
lemma Tser_succ (i : ℕ) : Tser (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Tser i := by
  unfold Tser
  have hterm : ∀ j : ℕ,
      (qB ^ ((i + 1) * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹
        = (qB ^ ((i + 1) * (j + 1)))⁻¹
          + cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹ := by
    intro j
    have hk := key_term (qB ^ (j + 1)) i (qpow_ne j) (one_sub_cqpow_ne (k := j + 1) (by omega))
    have e1 : qB ^ ((i + 1) * (j + 1)) = (qB ^ (j + 1)) ^ (i + 1) := by
      rw [← pow_mul, Nat.mul_comm]
    have e2 : qB ^ (i * (j + 1)) = (qB ^ (j + 1)) ^ i := by
      rw [← pow_mul, Nat.mul_comm]
    rw [e1, e2]; exact hk
  rw [tsum_congr hterm]
  have hsum_rest : Summable
      (fun j : ℕ => cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
    simp_rw [mul_assoc]
    exact (Tser_summable i).mul_left cB
  rw [Summable.tsum_add (geom_summable i) hsum_rest, geom_piece i]
  congr 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- **Piece II — the collapse**: `T_i = c^i · z + R_i`. Every auxiliary series is
`(rational) + (rational)·z`. Proved by induction on `i` from the recurrence. -/
theorem Tser_collapse (i : ℕ) : Tser i = cB ^ i * zB + Rrat i := by
  induction i with
  | zero => rw [Tser_zero, show Rrat 0 = 0 from rfl]; ring
  | succ i ih =>
      rw [Tser_succ, ih, show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl]
      ring

/-! ### Assembly building block: the product form of `Iₘ`

The lead factor `(1 − c·q^{m+n})⁻¹` is the `k = n` term of the `c`-product, so `Iₘ` separates into a
`q`-numerator times a clean `c`-product over `1..n`. This is the first algebraic step toward the
residue identity (then Piece I partial-fractions the `c`-product, Piece II collapses the result). -/

/-- `Iₘ = −(∏_{k=1}^{n-1}(1−q^{k−m}))·∏_{k=1}^{n}(1−c·q^{k+m})⁻¹` (for `n ≥ 1`). -/
lemma Iterm_prod_form (n m : ℕ) (hn : 1 ≤ n) :
    Iterm n m
      = -((∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
          * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + m))⁻¹) := by
  rw [Iterm, Finset.prod_mul_distrib,
    show ((m : ℤ) + n) = ((n : ℤ) + m) from by ring,
    show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) from by rw [Nat.sub_add_cancel hn],
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (n - 1) + 1), Nat.sub_add_cancel hn]
  ring

/-- **`q`-numerator expansion** `D_m = ∏_{k=1}^{n-1}(1−q^{k−m})` as a sum of monomials in `q^{−m}`:
each subset `t` contributes weight `(q^{−m})^{|t|}`. This produces exactly the `q^{−i·m}` weights
that the collapse `Tser_collapse` consumes (with `i = |t|`). -/
lemma Dterm_expand (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * ((qB ^ m)⁻¹) ^ t.card := by
  have hfac : ∀ k : ℕ, (1 : ℝ) - qB ^ ((k : ℤ) - m) = 1 + (-(qB ^ k)) * (qB ^ m)⁻¹ := by
    intro k
    rw [zpow_sub₀ qB_ne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **Piece IIIa — Cauchy expansion of the `c`-product** `∏_{k=1}^{n-1}(1 − c·q^{k+j})`, a direct
application of the Cauchy q-binomial theorem `qBin_cauchy` (reindex `k = 1 + i`, `t = −c·q^{j+1}`).
This is the first half of the first-form = second-form identity (Borwein Lemma 2); the second half is
the q-Lagrange identity `∑_j μ_j q^{jk} = q^k[n+k−1,n−1]_q` (Piece IIIb). -/
lemma cprod_cauchy {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ i ∈ Finset.range n,
          qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i) := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.prod_Ico_eq_prod_range]
  have hterm : ∀ k, (1 - cB * qB ^ (1 + k + j)) = 1 + qB ^ k * (-cB * qB ^ (j + 1)) := by
    intro k
    rw [show 1 + k + j = k + (j + 1) from by ring, pow_add]; ring
  rw [Finset.prod_congr rfl (fun k _ => hterm k), qBin_cauchy qB (-cB * qB ^ (j + 1)) (n - 1),
    Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul]
  ring

/-- Exponent bookkeeping `i(i−1)/2 + 2i = i(i+3)/2` (the `qBin_cauchy` exponent plus the two `q^i`
factors from the q-Lagrange step combine into the `pVal` exponent). -/
private lemma exp_iden (i : ℕ) : i * (i - 1) / 2 + 2 * i = i * (i + 3) / 2 := by
  rcases i with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1) * (m + 1 + 3) = (c + 2 * (m + 1)) + (c + 2 * (m + 1)) := by
      have : (m + 1) * (m + 1 + 3) = m * (m + 1) + 4 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- The q-Lagrange weight `μ_j = ∏_{l∈[1,n], l≠j}(1 − q^l/q^j)⁻¹` (independent of `c`, `m`). -/
noncomputable def muW (n j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (1 - qB ^ l / qB ^ j)⁻¹

/-- Borwein's q-Padé denominator in **first form** `pₙ = ∑_{j=1}^n μ_j·∏_{k=1}^{n-1}(1−c q^{k+j})`. -/
noncomputable def pFirst (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))

/-- **Piece III — first form = second form** (Borwein Lemma 2), conditional on the q-Lagrange
identity `qLag` (Piece IIIb, `aristotle/QLagrange.lean`). Assembled from the Cauchy expansion
`cprod_cauchy` + a finite sum swap + the exponent identity `exp_iden`. NO new axiom: `qLag` is a
hypothesis, to be discharged once IIIb is proved. -/
theorem pFirst_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    pFirst n = pVal n := by
  rw [pFirst, pVal]
  -- expand the c-product inside the j-sum via cprod_cauchy
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
        = ∑ i ∈ Finset.range n,
            muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i)) := by
    intro j _
    rw [cprod_cauchy hn j, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  -- pull the i-dependent factors out of the j-sum, leaving ∑_j μ_j (qB^j)^i
  have hfac : ∀ j ∈ Finset.Icc 1 n,
      muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i))
        = (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ i)
          * (muW n j * (qB ^ j) ^ i) := by
    intro j _
    rw [show (j + 1) * i = i + j * i from by ring, pow_add, pow_mul]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, qLag i hi]
  rw [show i * (i + 3) / 2 = i * (i - 1) / 2 + 2 * i from (exp_iden i).symm, pow_add]
  ring

/-! ### Assembly building block: the inner tail-sum collapse

In `Eterm n = ∑'_m Iₘ`, after the partial fraction (Piece I) and the `q`-numerator expansion
(`Dterm_expand`), the inner sum over `m ≥ n` of `q^{−i·m}·u_{m+j}` appears. Reindexing onto the
`Tser` grid and applying `Tser_collapse` turns it into `(rational) + (rational)·z`. This is the step
that makes the whole series collapse to `−pVal·z + (rational)`. -/

/-- The inner tail series `∑_{m≥0} q^{−i(n+m)}·u_{(n+m)+j}` appearing in the assembly. -/
noncomputable def Stail (i j n : ℕ) : ℝ :=
  ∑' m : ℕ, (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹

/-- **Tail collapse**: the inner series equals `q^{ij}·(Tser i − head)`, a finite reindex onto the
`Tser` grid. Combined with `Tser_collapse`, this is `q^{ij}·(c^i·z + R_i − head)`. -/
lemma Stail_collapse (i j n : ℕ) (hnj : 1 ≤ n + j) :
    Stail i j n
      = qB ^ (i * j) * (Tser i
          - ∑ m' ∈ Finset.range (n + j - 1),
              (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹) := by
  have hterm : ∀ m : ℕ,
      (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹
        = qB ^ (i * j) * ((qB ^ (i * ((m + (n + j - 1)) + 1)))⁻¹
            * (1 - cB * qB ^ ((m + (n + j - 1)) + 1))⁻¹) := by
    intro m
    have h1 : (m + (n + j - 1)) + 1 = (n + m) + j := by omega
    have hw : (qB ^ (i * (n + m)))⁻¹ = qB ^ (i * j) * (qB ^ (i * ((n + m) + j)))⁻¹ := by
      rw [show i * ((n + m) + j) = i * j + i * (n + m) from by ring, pow_add, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ qB_ne), one_mul]
    rw [h1, hw]; ring
  rw [Stail, tsum_congr hterm, tsum_mul_left]
  congr 1
  have hsum := Summable.sum_add_tsum_nat_add (n + j - 1) (Tser_summable i)
  rw [show Tser i = ∑' m : ℕ, (qB ^ (i * (m + 1)))⁻¹ * (1 - cB * qB ^ (m + 1))⁻¹ from rfl]
  linarith [hsum]

/-- **z-coefficient bridge**: `pFirst` re-expanded over the same subsets `t ⊆ [1,n−1]` that the
`q`-numerator `Dterm_expand` produces. This matches the assembly's z-coefficient
`−∑_t (∏_{k∈t}−q^k)·c^{|t|}·(∑_j μ_j (q^j)^{|t|})` exactly (since `∏_{k∈t}(−c·q^k) = (∏−q^k)·c^{|t|}`),
so the whole double series' z-part is `−pFirst·z = −pVal·z` — **without** needing the `e_i` or
q-Lagrange identities for the z-collection. -/
lemma pFirst_powerset (n : ℕ) :
    pFirst n = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-cB * qB ^ k)) * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
  rw [pFirst]
  have hexp : ∀ j, ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-cB * qB ^ k)) * (qB ^ j) ^ t.card := by
    intro j
    have hf : ∀ k, (1 : ℝ) - cB * qB ^ (k + j) = 1 + (-cB * qB ^ k) * qB ^ j := by
      intro k; rw [pow_add]; ring
    rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hexp j])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ### Piece I — the partial-fraction decomposition (Aristotle-harvested, verified axiom-clean)

`1/∏_{k=1}^n(1 − x·q^k) = ∑_{j=1}^n μ_j/(1 − x·q^j)` over the `n` distinct simple poles `x = q^{−j}`,
with `μ_j = ∏_{k≠j}(1 − q^k/q^j)⁻¹`. Proved via mathlib's `Lagrange.sum_basis` (the Lagrange basis
polynomials sum to `1`). Aristotle run `70eb84a6`; it correctly flagged that `n = 0` is false and
added `1 ≤ n`. In the assembly, specialize `x = c·q^m` so `1 − x·q^k = 1 − c·q^{m+k}` and
`μ_j = muW n j`. -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` (for `q > 1`). -/
lemma pf_injOn (q : ℝ) (hq : 1 < q) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  exact fun x hx y hy hxy => by rw [inv_inj, pow_right_inj₀] at hxy <;> linarith

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor. -/
lemma pf_factor (q : ℝ) (hq : 1 < q) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j=1}^n μ_j·∏_{k≠j}(1 − x·q^k) = 1` (Lagrange interpolation of the constant 1). -/
lemma pf_cleared (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor q hq x _ _]

/-- **Piece I — partial-fraction decomposition** `∏_{k=1}^n(1 − x·q^k)⁻¹ = ∑_j μ_j (1 − x·q^j)⁻¹`. -/
theorem partial_fraction (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/-! ### Negative-base (`1 < |q|`) partial-fraction decomposition.

Parallel to `pf_injOn`/`pf_factor`/`pf_cleared`/`partial_fraction`, but with the hypothesis weakened
from `1 < q` to `1 < |q|` so it covers negative bases `q ≤ −2`. The only sign-dependent step is node
distinctness (`pf_injOn_abs`), proved via strict monotonicity of `k ↦ |q|^k`; everything else is the
same Lagrange-basis argument. These feed the negative-base residue identity (`ItermG_triple` for
`1 < |q|` in `GeneralResidue.lean`). Left untouched: the `1 < q` originals (the axiom-clean q=2
`erdos_1050` chain routes through those). -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` for `1 < |q|` (any sign of `q`). -/
lemma pf_injOn_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  intro x _ y _ hxy
  simp only [inv_inj] at hxy
  have habs : |q| ^ x = |q| ^ y := by rw [← abs_pow, ← abs_pow, hxy]
  exact (StrictMono.injective (fun a b h => pow_lt_pow_right₀ hq h)) habs

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor (`q ≠ 0`). -/
lemma pf_factor_abs (q : ℝ) (hq0 : q ≠ 0) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  have hj : (q ^ j : ℝ) ≠ 0 := pow_ne_zero _ hq0
  have hk : (q ^ k : ℝ) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j} μ_j·∏_{k≠j}(1 − x·q^k) = 1` for `1 < |q|`. -/
lemma pf_cleared_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have hq0 : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn_abs q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor_abs q hq0 x _ _]

/-- **Piece I — partial-fraction decomposition for `1 < |q|`** (negative base allowed). -/
theorem partial_fraction_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared_abs q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/-! ### Final assembly: `Eterm n = −pVal n · zB + (rational)`

Combine all pieces. First `Iterm_triple` rewrites each `Iₘ` as a finite double sum (over subsets `t`
of the `q`-numerator and poles `j` of the partial fraction). Then `Eterm_eq_Stail` pulls the two
finite sums out of `∑'_m` (each inner series is `Stail`). Finally `Stail_collapse` + `Tser_collapse`
+ `pFirst_powerset` collect the z-coefficient as `−pFirst = −pVal`. -/

/-- Each `Iₘ` (here `M` general) as a finite double sum over subsets `t ⊆ [1,n−1]` and poles
`j ∈ [1,n]`, via `Iterm_prod_form` (split) + `partial_fraction` (Piece I) + `Dterm_expand`. -/
lemma Iterm_triple {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    Iterm n M
      = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ t, (-qB ^ k)) * muW n j
            * (((qB ^ M)⁻¹) ^ t.card * (1 - cB * qB ^ (M + j))⁻¹) := by
  have hpm : ∀ a : ℕ, cB * qB ^ M * qB ^ a = cB * qB ^ (M + a) := by
    intro a; rw [pow_add]; ring
  have hC : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
      = ∑ j ∈ Finset.Icc 1 n, muW n j * (1 - cB * qB ^ (M + j))⁻¹ := by
    have hconv : ∀ k : ℕ, (1 : ℝ) - cB * qB ^ ((k : ℤ) + M) = 1 - cB * qB ^ M * qB ^ k := by
      intro k
      have he : ((k : ℤ) + M) = ((k + M : ℕ) : ℤ) := by push_cast; ring
      rw [he, zpow_natCast, pow_add]; ring
    have hx : ∀ k, 1 ≤ k → k ≤ n → 1 - cB * qB ^ M * qB ^ k ≠ 0 := by
      intro k _ _; rw [hpm k]; exact one_sub_cqpow_ne (by omega)
    have hprodeq : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
        = (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ M * qB ^ k))⁻¹ := by
      simp only [hconv, Finset.prod_inv_distrib]
    rw [hprodeq, partial_fraction qB one_lt_qB n hn (cB * qB ^ M) hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpm j]
    rfl
  rw [Iterm_prod_form n M hn, hC, Dterm_expand n M]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `Stail`'s summand is summable (dominated by the geometric `(1/2)^m`). -/
lemma Stail_summable {n : ℕ} (hn : 1 ≤ n) (i j : ℕ) :
    Summable (fun m : ℕ => (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun m => (1 / 2 : ℝ) ^ m)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro m
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |(qB ^ (i * (n + m)))⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
    have h2 : |(1 - cB * qB ^ ((n + m) + j))⁻¹| ≤ qB ^ (-(((n + m) + j : ℕ) : ℤ)) := by
      have h := inv_cqpow_le (a := (((n + m) + j : ℕ) : ℤ)) (by exact_mod_cast (by omega : 1 ≤ (n + m) + j))
      rwa [zpow_natCast] at h
    have h3 : qB ^ (-(((n + m) + j : ℕ) : ℤ)) ≤ (1 / 2 : ℝ) ^ m := by
      rw [show (-(((n + m) + j : ℕ) : ℤ)) = -((m : ℤ) + (n + j)) from by push_cast; ring]
      calc qB ^ (-((m : ℤ) + (n + j))) ≤ qB ^ (-(m : ℤ)) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
        _ = (1 / 2 : ℝ) ^ m := qB_neg_zpow m
    calc |(qB ^ (i * (n + m)))⁻¹| * |(1 - cB * qB ^ ((n + m) + j))⁻¹|
        ≤ 1 * qB ^ (-(((n + m) + j : ℕ) : ℤ)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ m := by rw [one_mul]; exact h3

/-- **The pull-out**: `Eterm n` as a finite double sum of `Stail`'s, via `Iterm_triple` and pulling
the two finite sums out of `∑'_m` (`Summable.tsum_finsetSum`). -/
lemma Eterm_eq_Stail {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n := by
  have hStail : ∀ (t : Finset ℕ) (j : ℕ),
      (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹))
        = (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * ((qB ^ (t.card * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j; funext m
    rw [inv_pow, ← pow_mul, mul_comm (n + m) t.card]
  -- summability of each constant-scaled Stail summand
  have hsum : ∀ (t : Finset ℕ) (j : ℕ), Summable (fun m : ℕ =>
      (∏ k ∈ t, (-qB ^ k)) * muW n j
        * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j
    rw [hStail t j]
    exact ((Stail_summable hn t.card j).mul_left _)
  rw [Eterm, tsum_congr (fun m => Iterm_triple hn (n + m)), tsum_neg]
  congr 1
  rw [Summable.tsum_finsetSum (fun t _ => summable_sum (fun j _ => hsum t j))]
  apply Finset.sum_congr rfl; intro t _
  rw [Summable.tsum_finsetSum (fun j _ => hsum t j)]
  apply Finset.sum_congr rfl; intro j _
  rw [hStail t j, tsum_mul_left]
  congr 1

/-- The finite rational "head" removed when reindexing `Stail` onto the `Tser` grid. -/
noncomputable def headS (i j n : ℕ) : ℝ :=
  ∑ m' ∈ Finset.range (n + j - 1), (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹

/-- The explicit **rational correction** `Aₙ` of the residue identity `Eₙ = −pFirst·z + Aₙ`. -/
noncomputable def Acorr (n : ℕ) : ℝ :=
  -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
    (∏ k ∈ t, (-qB ^ k)) * muW n j
      * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n))

/-- **The residue identity** (contour-free, elementary): `Eₙ = −pFirst n · z + Aₙ`, with `Aₙ` an
explicit rational. Assembled from `Eterm_eq_Stail` (pull-out) + `Stail_collapse` (reindex) +
`Tser_collapse` (Piece II) + `pFirst_powerset` (z-coefficient). This is Borwein's Lemma 1 with the
first-form denominator `pFirst`; `pFirst_eq_pVal` (Piece III, mod q-Lagrange) connects it to `pVal`. -/
theorem Eterm_eq_pFirst {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -pFirst n * zB + Acorr n := by
  have key : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∀ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n
        = ((∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card)) * zB
          + (∏ k ∈ t, (-qB ^ k)) * muW n j
              * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    intro t _ j _
    rw [Stail_collapse t.card j n (by omega), Tser_collapse]
    rw [headS]
    ring
  -- z-coefficient (summed over t,j) equals pFirst n
  have hzcoef : ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card) = pFirst n := by
    rw [pFirst_powerset n]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpt : ∏ k ∈ t, (-cB * qB ^ k) = cB ^ t.card * ∏ k ∈ t, (-qB ^ k) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun k _ => by ring)
    have hqp : ((qB ^ j) ^ t.card : ℝ) = qB ^ (t.card * j) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpt, hqp]; ring
  rw [Eterm_eq_Stail hn,
    Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j hj => key t ht j hj))]
  simp_rw [Finset.sum_add_distrib]
  rw [neg_add, Acorr]
  congr 1
  rw [← hzcoef, neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]

/-- **Residue identity with the `pVal` denominator** (`Eₙ = −pVal n · z + Aₙ`), conditional on the
q-Lagrange identity `qLag` (Piece IIIb). This is exactly the shape the `residue_open` axiom feeds;
once `qLag` is discharged (Aristotle `aristotle/QLagrange.lean`) and the numerator integrality
`β^{2n}·Wₙ·Aₙ ∈ ℤ` (Borwein Lemma 3) is proved, `residue_open` becomes a theorem and `erdos_1050`
is axiom-clean. -/
theorem Eterm_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    Eterm n = -pVal n * zB + Acorr n := by
  rw [Eterm_eq_pFirst hn, pFirst_eq_pVal hn qLag]

/-! ### Toward Lemma 3 (numerator integrality): denominator-exposing forms

`Acorr`'s denominators come from `muW`, `Rrat`, `headS`. The first building block: the q-Lagrange
weight `μ_j` as `(q^j)^{n-1} / ∏_{l≠j}(q^j − q^l)` — a single explicit denominator `∏_{l≠j}(q^j−q^l)`
(a Vandermonde-type product). The eventual integrality argument shows `β^{2n}·Wₙ` clears these. -/

/-- `q^j − q^l ≠ 0` for `j ≠ l` (q-powers are distinct since `q > 1`). -/
lemma qpow_sub_ne {j l : ℕ} (hlj : l ≠ j) : (qB ^ j - qB ^ l : ℝ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  apply hlj
  rcases Nat.lt_trichotomy l j with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hgt))

/-- **Denominator-exposing closed form** of the q-Lagrange weight:
`μ_j = (q^j)^{|erase j|} · (∏_{l≠j}(q^j − q^l))⁻¹`. -/
lemma muW_closed (n j : ℕ) :
    muW n j = (qB ^ j) ^ ((Finset.Icc 1 n).erase j).card
      * (∏ l ∈ (Finset.Icc 1 n).erase j, (qB ^ j - qB ^ l))⁻¹ := by
  rw [muW]
  have hfac : ∀ l ∈ (Finset.Icc 1 n).erase j,
      (1 - qB ^ l / qB ^ j)⁻¹ = qB ^ j * (qB ^ j - qB ^ l)⁻¹ := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjne : (qB ^ j : ℝ) ≠ 0 := pow_ne_zero _ qB_ne
    have hsub : (qB ^ j - qB ^ l : ℝ) ≠ 0 := qpow_sub_ne hlj
    rw [show (1 - qB ^ l / qB ^ j : ℝ) = (qB ^ j - qB ^ l) / qB ^ j from by field_simp,
      inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    ← Finset.prod_inv_distrib]

/-- **Closed form of the rational correction term** `Rrat i = ∑_{l=1}^i c^{i-l}/(q^l − 1)`, exposing
its denominators `(q^l − 1)` and the `c`-powers (which clear under `3^{…}`). -/
lemma Rrat_closed (i : ℕ) : Rrat i = ∑ l ∈ Finset.Icc 1 i, cB ^ (i - l) / (qB ^ l - 1) := by
  induction i with
  | zero => simp [Rrat]
  | succ i ih =>
    rw [show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1), Nat.sub_self, pow_zero, Finset.mul_sum,
      add_comm (1 / (qB ^ (i + 1) - 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [show (i + 1) - l = (i - l) + 1 from by omega, pow_succ]
    ring

/-- **`headS` with integer denominators exposed**: each factor `(1 − c·q^{m'+1})⁻¹` clears to
`3·(3 − 8·q^{m'+1})⁻¹` (`c = 8/3`), surfacing the integer denominators `3 − 8·2^{m'+1}` (the same
factors as `CPint`) that `Wₙ`'s `∏(1 − c·q^k)` clears. -/
lemma headS_clear (i j n : ℕ) :
    headS i j n = ∑ m' ∈ Finset.range (n + j - 1),
      3 * (qB ^ (i * (m' + 1)))⁻¹ * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
  rw [headS]
  apply Finset.sum_congr rfl
  intro m' _
  have h : (1 - cB * qB ^ (m' + 1))⁻¹ = 3 * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
    rw [show (1 - cB * qB ^ (m' + 1) : ℝ) = (3 - 8 * qB ^ (m' + 1)) / 3 from by
      simp only [cB]; ring, inv_div, div_eq_mul_inv]
  rw [h]; ring

end JSP870.Erdos1050
