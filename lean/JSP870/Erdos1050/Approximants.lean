/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.Basic
import JSP870.Erdos1050.Criterion

/-!
# Explicit rational approximants to `S` (contour-free)

Borwein (1992) builds the approximants from a contour integral `Fₙ(q)`. The decisive observation
(buried in his Lemma 5 proof) is that `Fₙ` equals an **explicit convergent series** of finite
products — no contour integral is logically needed:

  `Fₙ = ∑_{m=n}^∞ Iₘ`,   `Iₘ = -(1 - c·q^{m+n})⁻¹ · ∏_{k=1}^{n-1} (1 - q^{k-m})·(1 - c·q^{k+m})⁻¹`.

We take this as the *definition* of the error term `Eₙ` and rebuild the irrationality argument on it.

## Reduction to the q-harmonic form
`S = ∑_{n≥0} 1/(2^{n+2}−3)` is, up to an affine map by nonzero rationals and a finite `q^{m}` shift,
the value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` (Borwein's normalized form with `q = 2`, `c = 8/3`,
`|c| > 2`). Irrationality is invariant under both operations, so `Irrational S ⟺ Irrational z`.

See `PENDING_WORK.md` for the full reduction chain and the obligation breakdown (O1–O4).
-/

namespace JSP870.Erdos1050
open scoped BigOperators
open Filter Topology Finset

/-- Borwein base `q = 2`. -/
def qB : ℝ := 2

/-- Reduced shift parameter `c = 8/3` (so `|c| > 2`), obtained from `c' = 1/3` shifted by `q^3`. -/
noncomputable def cB : ℝ := 8 / 3

/-- Denominator of the rational parameter `c = 8/3`. Used for the `β^{2n}` denominator clearing. -/
def βB : ℕ := 3

/-- The reduced q-harmonic target value `z = ∑_{j≥1} 1/(1 − c·q^j)` (with `q = 2`, `c = 8/3`).
`Irrational S ⟺ Irrational z`. -/
noncomputable def zB : ℝ := ∑' j : ℕ, (1 - cB * qB ^ (j + 1))⁻¹

/-- The `m`-th term of the explicit (contour-free) error series. For `m ≥ n` this is Borwein's
residue `Iₘ`. All factors use integer (`zpow`) exponents so that `q^{k-m}` makes sense. -/
noncomputable def Iterm (n m : ℕ) : ℝ :=
  -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ *
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹

/-- The error term `Eₙ = Fₙ = ∑_{m≥n} Iₘ`, reindexed as `∑_{j≥0} I_{n}(n+j)`. -/
noncomputable def Eterm (n : ℕ) : ℝ := ∑' j : ℕ, Iterm n (n + j)

/-! ### Numeric facts about the base parameters `q = 2`, `c = 8/3`. -/

lemma qB_pos : (0 : ℝ) < qB := by norm_num [qB]
lemma one_lt_qB : (1 : ℝ) < qB := by norm_num [qB]
lemma qB_ne : qB ≠ 0 := ne_of_gt qB_pos
lemma cB_pos : (0 : ℝ) < cB := by norm_num [cB]
lemma two_lt_cB : (2 : ℝ) < cB := by norm_num [cB]

/-- `q^k ≥ 2` for `k ≥ 1` (natural power version). -/
lemma two_le_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ≤ qB ^ k := by
  calc (2 : ℝ) = qB ^ 1 := by norm_num [qB]
    _ ≤ qB ^ k := pow_le_pow_right₀ (le_of_lt one_lt_qB) hk

/-- `q^a ≥ q ≥ 2` for `a ≥ 1`. -/
lemma two_le_zpow {a : ℤ} (ha : 1 ≤ a) : (2 : ℝ) ≤ qB ^ a := by
  calc (2 : ℝ) = qB ^ (1 : ℤ) := by norm_num [qB]
    _ ≤ qB ^ a := zpow_le_zpow_right₀ (le_of_lt one_lt_qB) ha

/-- Each `c·q^a − 1` (for `a ≥ 1`) dominates `q^a`, so its inverse is at most `q^{-a}`. -/
lemma inv_cqpow_le {a : ℤ} (ha : 1 ≤ a) : |(1 - cB * qB ^ a)⁻¹| ≤ qB ^ (-a) := by
  have hqa : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hqpos : (0 : ℝ) < qB ^ a := zpow_pos qB_pos a
  -- `c·q^a − 1 ≥ q^a > 0`
  have hge : qB ^ a ≤ cB * qB ^ a - 1 := by nlinarith [hqa, hqpos, two_lt_cB]
  have hpos : (0 : ℝ) < cB * qB ^ a - 1 := lt_of_lt_of_le hqpos hge
  have habs : |(1 - cB * qB ^ a)⁻¹| = (cB * qB ^ a - 1)⁻¹ := by
    rw [abs_inv]
    congr 1
    rw [abs_of_neg (by linarith)]
    ring
  rw [habs, zpow_neg]
  exact inv_anti₀ hqpos hge

/-- Each product factor `(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` has absolute value at most `1/2`
(for `1 ≤ k < m`). -/
lemma factor_bound {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 : ℝ) / 2 := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) :=
    inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) ≤ (1 : ℝ) / 2 := by
    calc qB ^ (-((k : ℤ) + m)) ≤ qB ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
      _ = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * (1 / 2) := mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by ring

/-- **Crude per-term bound.** For `1 ≤ n ≤ m`, `|Iₘ| ≤ q^{-(m+n)}·(1/2)^{n-1}`. The leading
factor carries the geometric `m`-decay; the `(n−1)` product factors are each `≤ 1/2`. (Enough for
summability and non-vanishing; the sharp super-exponential bound is the separate error obligation.) -/
lemma Iterm_abs_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ qB ^ (-((m : ℤ) + n)) * (1 / 2) ^ (n - 1) := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ qB ^ (-((m : ℤ) + n)) :=
    inv_cqpow_le (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 / 2) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), (1 / 2 : ℝ) :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_bound hk.1 (by omega))
      _ = (1 / 2 : ℝ) ^ (Finset.Icc 1 (n - 1)).card := by rw [Finset.prod_const]
      _ = (1 / 2 : ℝ) ^ (n - 1) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ qB ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos qB_pos _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- `q^{-j} = (1/2)^j`. -/
lemma qB_neg_zpow (j : ℕ) : qB ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
  rw [zpow_neg, zpow_natCast, show qB = 2 from rfl,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]

/-- The reindexed term `I_n(n+j)` is bounded by `(1/2)^j` — enough for absolute summability. -/
lemma Iterm_shift_le {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : |Iterm n (n + j)| ≤ (1 / 2 : ℝ) ^ j := by
  have h := Iterm_abs_le hn (Nat.le_add_right n j)
  have hexp : qB ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ qB ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt one_lt_qB)
    push_cast; omega
  have hpow1 : (1 / 2 : ℝ) ^ (n - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc |Iterm n (n + j)| ≤ qB ^ (-(((n + j : ℕ) : ℤ) + n)) * (1 / 2) ^ (n - 1) := h
    _ ≤ qB ^ (-(j : ℤ)) * 1 :=
        mul_le_mul hexp hpow1 (by positivity) (le_of_lt (zpow_pos qB_pos _))
    _ = (1 / 2) ^ j := by rw [mul_one, qB_neg_zpow]

/-- The error series `Eₙ = ∑_{j} I_n(n+j)` is summable. -/
lemma Eterm_summable {n : ℕ} (hn : 1 ≤ n) : Summable (fun j => Iterm n (n + j)) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ j)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro j; rw [Real.norm_eq_abs]; exact Iterm_shift_le hn j

/-! ### Non-vanishing of the error (Borwein's Lemma 5).

For `q = 2`, `c = 8/3 > 1`, every term `Iₘ` (`m ≥ n`) has the *same* nonzero sign `(-1)^{n-1}`:
the leading factor `(1 − c·q^{m+n})⁻¹` is negative, and each of the `n−1` product factors
`(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` is negative. A sum of same-sign nonzero terms cannot vanish. -/

/-- The leading factor `(1 − c·q^a)⁻¹` is negative for `a ≥ 1`. -/
lemma leading_neg {a : ℤ} (ha : 1 ≤ a) : (1 - cB * qB ^ a)⁻¹ < 0 := by
  have h2 : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hneg : (1 - cB * qB ^ a) < 0 := by nlinarith [h2, two_lt_cB, zpow_pos qB_pos a]
  exact inv_neg''.mpr hneg

/-- Each product factor is negative for `1 ≤ k < m`. -/
lemma factor_neg {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ < 0 := by
  have hnum : 0 < 1 - qB ^ ((k : ℤ) - m) := by
    have hle : qB ^ ((k : ℤ) - m) ≤ qB ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
    have heq : qB ^ (-1 : ℤ) = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
    rw [heq] at hle; linarith
  exact mul_neg_of_pos_of_neg hnum (leading_neg (by omega))

/-- `(-1)^{n-1}` times the product of the `n−1` (negative) factors is positive. -/
lemma prod_factor_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h1 : (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) := by
    rw [Finset.prod_const, hcard]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hf := factor_neg hk.1 (show k < m by omega)
  linarith

/-- The sign of `Iₘ` (for `m ≥ n ≥ 1`) is exactly `(-1)^{n-1}`, and it is nonzero. -/
lemma Iterm_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : 0 < (-1 : ℝ) ^ (n - 1) * Iterm n m := by
  rw [Iterm]
  have hL : (1 - cB * qB ^ ((m : ℤ) + n))⁻¹ < 0 := leading_neg (by omega)
  have hP := prod_factor_sign hn hnm
  have hnegL : (0 : ℝ) < -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ := by linarith
  have := mul_pos hnegL hP
  -- v4.31: `convert … using 1` now also emits the `LT` instance-equality goal
  -- (`Real.instLT = Real.instPreorder.toLT`); close it by `rfl`, the algebra by `ring`.
  convert this using 1 <;> first | rfl | ring

/-! ### Sharp super-exponential error bound (Borwein's Lemma 4).

The decisive estimate. Using `|1 − q^{k−m}| ≤ 1` and `(c·q^a − 1)⁻¹ ≤ q^{-a}`,

  `|Iₘ| ≤ q^{-(m+n)}·∏_{k=1}^{n-1} q^{-(k+m)} = q^{-(n + T + n·m)}`,  `T = ∑_{k=1}^{n-1} k`,

which factors as `Cₙ·rⁿ` with `r = q^{-n} ∈ (0,1)`. Summing the geometric tail gives
`|Eₙ| ≤ 2·Cₙ·q^{-n²}`, super-exponential decay — enough to beat the denominator growth `Wₙ`. -/

/-- Tight per-factor bound: `|(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹| ≤ (q^{k+m})⁻¹` for `1 ≤ k < m`. -/
lemma factor_abs_le {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (qB ^ (k + m))⁻¹ := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) := inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) = (qB ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast qB (k + m), Nat.cast_add]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * qB ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (qB ^ (k + m))⁻¹ := by rw [one_mul, h3]

/-- Sharp per-term bound in product form. -/
lemma Iterm_abs_le_sharp {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ (qB ^ (m + n))⁻¹ := by
    have h := inv_cqpow_le (a := (m : ℤ) + n) (by omega)
    have he : qB ^ (-((m : ℤ) + n)) = (qB ^ (m + n))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast qB (m + n), Nat.cast_add]
    rwa [he] at h
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
    intro k hk; rw [Finset.mem_Icc] at hk
    exact factor_abs_le hk.1 (by omega)
  exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos qB_pos _)))

/-- Exponent bookkeeping: `(m+n) + ∑_{k=1}^{n-1}(k+m) = (n + ∑_{k=1}^{n-1} k) + n·m` for `n ≥ 1`.
The `n·m` term is the source of the super-exponential (`q^{-n·m}`) decay. -/
lemma exp_identity {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    (m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)
      = (n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
  have hmul : (n - 1) * m + m = n * m := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m hn)]
  omega

/-- **Closed-form sharp per-term bound** (Borwein Lemma 4 core): `|Iₘ| ≤ Cₙ·(q^{-n})^m` with
`Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Geometric in `m` with ratio `q^{-n} ≤ 1/2`, so the tail sum is
super-exponentially small. -/
lemma Iterm_abs_le_geom {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m := by
  refine (Iterm_abs_le_sharp hn hnm).trans (le_of_eq ?_)
  have hL : (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹
      = (qB ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
  have hR : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m
      = (qB ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- **Lemma 4 (error bound), `Eₙ` half.** Summing the geometric per-term bound:
`|Eₙ| ≤ Cₙ·(q^{-n})ⁿ·(1 − q^{-n})⁻¹` with `Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Since `(q^{-n})ⁿ = q^{-n²}`
and `Cₙ = q^{-(n + n(n-1)/2)}`, this is `≈ q^{-3n²/2}` — super-exponential, as in Borwein. -/
lemma Eterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
        * (1 - (qB ^ n)⁻¹)⁻¹ := by
  set r : ℝ := (qB ^ n)⁻¹ with hr_def
  set Cn : ℝ := (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos qB_pos n))
  have hqn1 : (1 : ℝ) < qB ^ n := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ n := pow_le_pow_right₀ (le_of_lt one_lt_qB) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |Iterm n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => Iterm_shift_le hn j)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have h1 : |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => Iterm n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [Eterm, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |Iterm n (n + j)| ≤ Cn * r ^ (n + j) := fun j =>
    Iterm_abs_le_geom hn (Nat.le_add_right n j)
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |Iterm n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed form of the error bound: `|Eₙ| ≤ 2·(q^{n + ∑_{k<n}k + n²})⁻¹`. The exponent
`n + (n−1)n/2 + n² = (3n² + n)/2` is Borwein's `3n²/2` decay (up to lower order). -/
lemma Eterm_abs_le' {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  refine (Eterm_abs_le hn).trans ?_
  have hC : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ qB ^ n := two_le_pow hn
  have h1 : (qB ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (qB ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (qB ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos qB_pos _))
  calc (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n * (1 - (qB ^ n)⁻¹)⁻¹
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * (1 - (qB ^ n)⁻¹)⁻¹ := by rw [hC]
    _ ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by ring

/-- **Lemma 5 (non-vanishing).** `Eₙ ≠ 0` for `n ≥ 1`. -/
lemma Eterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Eterm n ≠ 0 := by
  have hsum : Summable (fun j => (-1 : ℝ) ^ (n - 1) * Iterm n (n + j)) :=
    (Eterm_summable hn).mul_left _
  have hpos : ∀ j, 0 < (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    fun j => Iterm_sign hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, Iterm n (n + j)) = Eterm n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/-! ### The denominator-clearing factor `Wₙ` and the assembly into irrationality. -/

lemma one_sub_cqpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - cB * qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk, two_lt_cB, pow_pos qB_pos k])

lemma one_sub_qpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk])

/-- The clearing factor `Wₙ = (n−2)!·∏_{k=1}^n (1 − c·q^k)·∏_{k=⌈n/2⌉}^n (1 − q^k)` (Borwein's
`wₙ` without the `pₙ` factor; `Wₙ·Fₙ = wₙ·z + sₙ`). -/
noncomputable def Wterm (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)
    * (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k))
    * (∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k))

/-- `Wₙ ≠ 0` for `n ≥ 1`: a nonzero factorial times two products of nonzero factors. -/
lemma Wterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Wterm n ≠ 0 := by
  rw [Wterm]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_cqpow_ne hk.1
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    -- `k ≥ ⌈n/2⌉ ≥ 1` since `n ≥ 1`
    exact one_sub_qpow_ne (by omega)

/-- **Wₙ growth bound** (Borwein Lemma 3 estimate). `|Wₙ| ≤ (n−2)!·cⁿ·(q^{∑_{k≤n}k})²`. Each
`|1 − c·q^k| ≤ c·q^k` and `|1 − q^k| ≤ q^k`; the second product (over `⌈n/2⌉..n`) is bounded by the
full product over `1..n`. -/
lemma Wterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Wterm n| ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
        * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hfac : (0:ℝ) ≤ (Nat.factorial (n-2) : ℝ) := by positivity
  have hqS : (0:ℝ) ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt qB_pos) _
  rw [Wterm, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)| ≤ cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - cB * qB ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, cB * qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_neg (by nlinarith [two_le_pow hk.1, two_lt_cB, pow_pos qB_pos k] :
            (1 - cB * qB ^ k) < 0)]
          nlinarith [pow_pos qB_pos k, cB_pos]
      _ = cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)| ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - qB ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_nonpos (by nlinarith [two_le_pow (show 1 ≤ k by omega)] : (1 - qB ^ k) ≤ 0)]
          linarith
      _ = qB ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := prod_pow_eq_pow_sum _ _ _
      _ ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) :=
          pow_le_pow_right₀ (le_of_lt one_lt_qB)
            (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (le_refl n)))
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * (cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg (le_of_lt cB_pos) n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by ring

/- **O1 — Borwein Lemmas 1+2+3.** Formerly a monolithic axiom `borwein_integrality` lived here; it is
now a fully machine-checked THEOREM (`Lemma3.lean`). Lemma 1 (residue identity) is proved elementarily
(`Residue.lean`, `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md`); Lemma 2 (denominator integrality) is
`Bden_cast` (`Integrality.lean`, via `qBin_cauchy`); Lemma 3 (numerator integrality) is proved
elementarily (`Lemma3.lean`, via q-Lagrange + a 2-adic/odd-denominator clearing for `N_h`). The
headline `erdos_1050` is axiom-clean. -/

/-- Gauss' formula over `Icc 1 n`: `2·∑_{k=1}^n k = n(n+1)`. -/
lemma gauss_Icc (n : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 n, k) = n * (n + 1) := by
  have hconv : (∑ k ∈ Finset.Icc 1 n, k) = ∑ k ∈ Finset.range (n + 1), k := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
    · intro x hx hx2; rw [Finset.mem_range] at hx; rw [Finset.mem_Icc] at hx2; omega
  rw [hconv, mul_comm, Finset.sum_range_id_mul_two, Nat.add_sub_cancel, Nat.mul_comm]

/-- **The combine majorant** (Borwein Lemma 4, all factors assembled). The cleared error is bounded
by `2·(n−2)!·(9c)ⁿ·(q^{∑_{k<n}k})⁻¹`: the `q^{2∑_{k≤n}k}` from `Wₙ` and `β^{2n}=9ⁿ` cancel against
`Eₙ`'s `q^{-(n + ∑_{k<n}k + n²)}` decay, leaving the super-exponential `(q^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_le {n : ℕ} (hn : 1 ≤ n) :
    |(βB : ℝ) ^ (2 * n) * Wterm n * Eterm n|
      ≤ 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hβ : (βB : ℝ) ^ (2 * n) = (9 : ℝ) ^ n := by rw [pow_mul]; norm_num [βB]
  have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [← two_mul, gauss_Icc n]; ring
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by omega
  have hq : qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos qB_pos _)), one_mul]
  have hWnn : (0:ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
      * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (le_of_lt cB_pos) n)) ?_) ?_ <;> exact pow_nonneg (le_of_lt qB_pos) _
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  calc (βB : ℝ) ^ (2 * n) * |Wterm n| * |Eterm n|
      ≤ (βB : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * cB ^ n
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (Eterm_abs_le' hn) (abs_nonneg _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hWnn)
        exact mul_le_mul_of_nonneg_left (Wterm_abs_le hn) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hβ, mul_pow, ← hq]; ring

/-- `∑_{k=1}^{n-1} k = n(n−1)/2` (Gauss, lower form). -/
lemma gauss_Icc' (n : ℕ) : ∑ k ∈ Finset.Icc 1 (n - 1), k = n * (n - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; simp
  · have h := gauss_Icc (n - 1)
    rw [Nat.sub_add_cancel hn0, Nat.mul_comm (n - 1) n] at h
    omega

/-! ### The asymptotic `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹ → 0` (auto-formalized by Aristotle, verified
axiom-clean in our kernel). Super-exponential `(q^{n(n-1)/2})⁻¹` decay beats `(n-2)!·Cⁿ`; proved
by the ratio test (consecutive ratio `(n−1)C/qⁿ → 0`). -/

/-- Triangle-number recurrence `T(n+1) = T(n) + n`. -/
private lemma tri_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n := by
  have e : ∀ k : ℕ, k * (k - 1) / 2 = k.choose 2 := fun k => (Nat.choose_two_right k).symm
  rw [e, e, Nat.choose_succ_succ n 1]
  simp [Nat.choose_one_right]
  omega

private lemma fact_step (n : ℕ) (hn : 2 ≤ n) :
    Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.factorial_succ]

/-- The Borwein cleared-error majorant `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹`. -/
private noncomputable def fseq (q C : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹

private lemma fseq_pos (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) : 0 < fseq q C n := by
  have hq0 : 0 < q := by linarith
  unfold fseq; positivity

private lemma fseq_ratio (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) (hn : 2 ≤ n) :
    fseq q C (n + 1) / fseq q C n = (↑(n - 1)) * C * (q ^ n)⁻¹ := by
  have hq0 : 0 < q := by linarith
  unfold fseq
  have hfn : (n + 1) - 2 = n - 1 := by omega
  rw [hfn, fact_step n hn, tri_succ n, pow_add]
  have hpos1 : (0 : ℝ) < q ^ (n * (n - 1) / 2) := by positivity
  have hpos2 : (0 : ℝ) < q ^ n := by positivity
  have hC0 : C ≠ 0 := ne_of_gt hC
  push_cast; field_simp; ring

private lemma ratio_tendsto (q C : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) atTop (𝓝 0) := by
  have hr : |q⁻¹| < 1 := by
    rw [abs_of_pos (by positivity), inv_lt_one_iff₀]; right; exact hq
  have hbase : Tendsto (fun n : ℕ => (↑n : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hsq : Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) := by
    apply squeeze_zero (f := fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n)
      (g := fun n => (↑n : ℝ) * (q⁻¹) ^ n) (fun n => by positivity) ?_ hbase
    intro n
    have hb : (0 : ℝ) ≤ (q⁻¹) ^ n := by positivity
    have hle : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    nlinarith [hle, hb]
  have heq : (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹)
      = (fun n : ℕ => C * ((↑(n - 1) : ℝ) * (q⁻¹) ^ n)) := by
    funext n; rw [inv_pow]; ring
  rw [heq]; simpa using hsq.const_mul C

/-- **The combine asymptotic** (Aristotle, verified). -/
theorem combine_asymptotic (q C : ℝ) (hq : 1 < q) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹)
      atTop (nhds 0) := by
  have hsummable : Summable (fseq q C) := by
    apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    · filter_upwards with n using ne_of_gt (fseq_pos q C hq hC n)
    · have hcongr : (fun n : ℕ => ‖fseq q C (n + 1)‖ / ‖fseq q C n‖)
          =ᶠ[atTop] (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        rw [Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _)),
            Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _))]
        exact fseq_ratio q C hq hC n hn
      exact (ratio_tendsto q C hq).congr' hcongr.symm
  exact hsummable.tendsto_atTop_zero

/-- **O2 — error → 0 (Borwein Lemma 4, combine step), PROVED.** The cleared error `β^{2n}·Wₙ·Eₙ → 0`.
Squeeze: `cleared_error_le` bounds `|β^{2n}WₙEₙ|` by `2·(n-2)!·(9c)ⁿ·(q^{n(n-1)/2})⁻¹`, which
`combine_asymptotic` sends to `0`. -/
lemma cleared_error_tendsto :
    Filter.Tendsto (fun n => (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n) Filter.atTop (nhds 0) := by
  have hg : Tendsto (fun n => 2 * ((Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
      * (qB ^ (n * (n - 1) / 2))⁻¹)) atTop (𝓝 0) := by
    simpa using (combine_asymptotic qB (9 * cB) one_lt_qB (by have := cB_pos; positivity)).const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_le hn
  rw [gauss_Icc' n] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **O4 — reduction `S ↔ z`, PROVED.** Per-term `(1 − c·q^{j+1})⁻¹ = −3/(2^{j+4}−3)`, so
`zB = −3·∑_{j} 1/(2^{(j+2)+2}−3) = −3·(S − 1 − 1/5) = −3·S + 18/5`. Irrationality is invariant
under the nonzero-rational affine map. -/
lemma irrational_S_iff_zB : Irrational S ↔ Irrational zB := by
  -- Summability (auto-formalized by Aristotle, verified axiom-clean; compare `∑ 2^{-n}`);
  -- lifted to `S_summable` in `Basic.lean`.
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := S_summable
  have hkey : zB = -3 * S + 18 / 5 := by
    have hterm : ∀ j : ℕ,
        (1 - cB * qB ^ (j + 1))⁻¹ = -3 * ((1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) := by
      intro j
      have hp2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hexp : (2 : ℝ) ^ ((j + 2) + 2) = 8 * 2 ^ (j + 1) := by
        rw [show (j + 2) + 2 = (j + 1) + 3 from by ring, pow_add]; ring
      rw [hexp]; simp only [cB, qB]
      have hd2 : (1 : ℝ) - 8 / 3 * 2 ^ (j + 1) ≠ 0 := ne_of_lt (by nlinarith [hp2])
      have hd1 : (8 : ℝ) * 2 ^ (j + 1) - 3 ≠ 0 := ne_of_gt (by nlinarith [hp2])
      rw [inv_eq_one_div, mul_one_div, div_eq_div_iff hd2 hd1]
      ring
    rw [zB, tsum_congr hterm, tsum_mul_left]
    have hsum1 : Summable (fun i : ℕ => (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3)) :=
      hsummable.comp_injective (add_left_injective 1)
    have e1 : S = (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3)
        + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3) := hsummable.tsum_eq_zero_add
    have e2 : (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3))
        = (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3)
          + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := hsum1.tsum_eq_zero_add
    have htail : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) = S - 6 / 5 := by
      have hconv : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3))
          = ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := rfl
      rw [hconv]
      have hSf0 : (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3) = 1 := by norm_num
      have hSf1 : (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3) = 1 / 5 := by norm_num
      rw [hSf0] at e1
      rw [hSf1] at e2
      linarith [e1, e2]
    rw [htail]; ring
  rw [hkey, show (-3 : ℝ) * S + 18 / 5 = ((-3 : ℤ) : ℝ) * S + ((18 / 5 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff, irrational_intCast_mul_iff]
  exact ⟨fun h => ⟨by decide, h⟩, And.right⟩

/- `irrational_zB` and the headline `erdos_1050 : Irrational S` are assembled in `Integrality.lean`
(they need the `pVal`-based `borwein_integrality` theorem, which is downstream of `Pade.lean`). -/

end JSP870.Erdos1050
