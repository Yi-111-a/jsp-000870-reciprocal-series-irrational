/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import JSP870.Erdos1050.QBinom

/-!
# The q-Lagrange identity (Borwein Lemma 2, "Piece IIIb")

With the q-Lagrange weights `μ_j = ∏_{l≠j}(1 − q^l/q^j)⁻¹` (j,l ∈ [1,n]) and `1 < q`, for any `k`:

    ∑_{j=1}^n  μ_j · (q^j)^k   =   q^k · [n+k−1, n−1]_q .

This is the harder half of Borwein's first-form = second-form identity for the q-Padé denominator
`pₙ`; together with the Cauchy expansion (`cprod_cauchy`) it gives `pFirst n = pVal n`, discharging
the qLag hypothesis of `Eterm_eq_pVal` and the first clause of `residue_open`.

**Provenance**: auto-formalized by Harmonic's Aristotle (run `e53ca6e8`), then ported onto the repo's
`qBin` (which is the *same* q-Pascal recurrence Aristotle used) and verified axiom-clean in our kernel
(`#print axioms qLagrange = [propext, Classical.choice, Quot.sound]`).

The proof recognizes the LHS as a **divided-difference** sum `Dsum x s m = ∑_j (x j)^m/∏_{l≠j}(x j−x l)`
of the monomial `t^m` at the nodes `x j = q^j`, which satisfies the recurrence `Dsum_rec`, vanishes in
low degree (`Dsum_low`), and has the closed form `Dsum_main` by a double induction using q-Pascal.
-/

open Finset

namespace JSP870.Erdos1050

/-- The product `∏_{l ∈ s, l ≠ j} (x j - x l)`, the denominator of the `j`-th divided-difference
weight. -/
noncomputable def Wprod (x : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) : ℝ :=
  ∏ l ∈ s.erase j, (x j - x l)

/-- The divided difference of the monomial `t^m` at the nodes `x j`, `j ∈ s`. -/
noncomputable def Dsum (x : ℕ → ℝ) (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ s, (x j) ^ m / Wprod x s j

/-- The node function `j ↦ q^j` is injective when `1 < q`. -/
lemma qpow_injective (q : ℝ) (hq : 1 < q) : Function.Injective (fun j : ℕ => q ^ j) := by
  exact fun a b h => le_antisymm ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop ) ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop )

/-- The node function `j ↦ q^j` is injective when `1 < |q|` (any sign of `q`). `q^a = q^b` ⟹
`|q|^a = |q|^b` ⟹ `a = b`. The entry point for the negative-base (`q ≤ −2`) q-Lagrange identity. -/
lemma qpow_injective_abs (q : ℝ) (hq : 1 < |q|) : Function.Injective (fun j : ℕ => q ^ j) := by
  intro a b h
  have habs : |q| ^ a = |q| ^ b := by rw [← abs_pow, ← abs_pow]; exact congrArg abs h
  exact qpow_injective |q| hq habs

/-- The fundamental divided-difference recurrence: removing any node `a ∈ s`. -/
lemma Dsum_rec (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (a : ℕ) (ha : a ∈ s)
    (m : ℕ) :
    Dsum x s (m + 1) = Dsum x (s.erase a) m + x a * Dsum x s m := by
  unfold Dsum Wprod;
  have h_split : ∑ j ∈ s, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = ∑ j ∈ s.erase a, x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
    have h_split : ∀ j ∈ s.erase a, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
      intro j hj; rw [ Finset.prod_eq_prod_sdiff_singleton_mul <| Finset.mem_erase_of_ne_of_mem ( by aesop ) ha ] ; ring_nf;
      rw [ show ( s.erase a ).erase j = s.erase j \ { a } by ext; aesop ] ; ring_nf;
      grind;
    rw [ ← Finset.sum_congr rfl h_split, Finset.sum_erase_eq_sub ha ] ; aesop;
  simp_all +decide [ mul_sub, sub_div, pow_succ, mul_div_assoc, Finset.mul_sum _ _ _ ];
  grind

/-- For at least two distinct nodes, `∑_j 1/∏_{l≠j}(x j - x l) = 0`. -/
lemma Dsum_zero (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (hs : 2 ≤ s.card) :
    Dsum x s 0 = 0 := by
  induction' s using Finset.strongInduction with s ih;
  by_cases h_two_elements : s.card = 2;
  · rw [ Finset.card_eq_two ] at h_two_elements;
    rcases h_two_elements with ⟨ a, b, hab, rfl ⟩ ; unfold Dsum; simp +decide [ hab ] ; ring_nf;
    unfold Wprod; simp +decide [ *, Finset.prod ] ; ring_nf;
    rw [ show -x a + x b = - ( x a - x b ) by ring, inv_neg ] ; ring;
  · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ s, ∃ b ∈ s, a ≠ b :=
      one_lt_card.mp hs
    have h_rec_a : Dsum x s 1 = Dsum x (s.erase a) 0 + x a * Dsum x s 0 := by
      exact Dsum_rec x hx s a ha 0
    have h_rec_b : Dsum x s 1 = Dsum x (s.erase b) 0 + x b * Dsum x s 0 := by
      exact Dsum_rec x hx s b hb 0;
    grind +splitIndPred

/-- The divided difference of a monomial of degree below `card - 1` vanishes. -/
lemma Dsum_low (x : ℕ → ℝ) (hx : Function.Injective x) :
    ∀ (s : Finset ℕ) (m : ℕ), m + 1 < s.card → Dsum x s m = 0 := by
  intro s m hm;
  induction' m with m ih generalizing s;
  · exact Dsum_zero x hx s hm;
  · obtain ⟨ a, ha ⟩ := Finset.card_pos.mp ( by linarith );
    rw [ Dsum_rec x hx s a ha m ];
    rw [ ih s ( by linarith ), ih ( s.erase a ) ( by rw [ Finset.card_erase_of_mem ha ] ; omega ), MulZeroClass.mul_zero, add_zero ]

/-- The closed form of the divided difference of `t^{N+k}` at the nodes `q, q^2, …, q^{N+1}`.
Only node *injectivity* is needed (the Gaussian-binomial closed form is a polynomial identity), so this
holds for any `q` with `q^j` injective — both `1 < q` and `1 < |q|` (`q ≤ −2`). -/
lemma Dsum_main (q : ℝ) (hinj : Function.Injective (fun j : ℕ => q ^ j)) :
    ∀ N k : ℕ, Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k)
      = q ^ k * qBin q (N + k) N := by
  intros N k
  induction' N with N ih generalizing k;
  · unfold Dsum Wprod qBin; norm_num;
  · induction' k with k ihk;
    · have := Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) N;
      simp_all +decide;
      rw [ show Dsum ( fun j => q ^ j ) ( Icc 1 ( N + 2 ) ) N = 0 from _ ] ; norm_num [ qBin_self ];
      · -- v4.31: `convert … using 1` no longer auto-unifies `Ico 1 (N+2)` with
        -- `Icc 1 (N+1)`, so it leaves a separate interval-reindex goal alongside the
        -- numeric one. Discharge both explicitly.
        convert ih 0 using 1
        · simp only [Nat.add_zero]
          rw [show Finset.Ico 1 (N + 2) = Finset.Icc 1 (N + 1) from by
                ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
        · norm_num [qBin_self]
      · convert Dsum_low ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) N _ using 1 ; simp +arith +decide;
    · have h_rec : Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k + 1) = Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k + 1) + q ^ (N + 2) * Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k) := by
        convert Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) ( N + 1 + k ) using 1;
        simp +arith +decide;
        rfl;
      have hpascal := qBin_succ_succ q (N + k + 1) N
      grind +locals [qBin_succ_succ]

/-- The original q-Lagrange LHS rewritten as a divided-difference sum. Needs only `q ≠ 0`. -/
lemma lhs_eq_Dsum (q : ℝ) (hq0 : q ≠ 0) (n : ℕ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = Dsum (fun j => q ^ j) (Finset.Icc 1 n) (n - 1 + k) := by
  refine' Finset.sum_congr rfl fun j hj => _;
  have h_term : ∀ l ∈ Finset.erase (Finset.Icc 1 n) j, (1 - q ^ l / q ^ j)⁻¹ = q ^ j / (q ^ j - q ^ l) := by
    intro l hl; rw [ one_sub_div ( pow_ne_zero j hq0 ) ] ; norm_num;
  rw [ Finset.prod_congr rfl h_term, Finset.prod_div_distrib, Finset.prod_const, Finset.card_erase_of_mem hj, Nat.card_Icc, ( by aesop : n - 1 = n - 1 ) ] ; ring!;

/-- **The q-Lagrange identity** (`1 < q`).  (The hypothesis `hk : k ≤ n - 1` is unnecessary — the identity
holds for every `k` — but is kept for faithfulness with the `residue_open` clause.) -/
theorem qLagrange (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  rw [lhs_eq_Dsum q (by linarith) n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

/-- **The q-Lagrange identity for `1 < |q|`** (both signs of `q`, e.g. negative base `q ≤ −2`). Same
divided-difference proof, using `qpow_injective_abs` for node distinctness. A brick toward the
negative-base discharge of `borwein_approximants`. -/
theorem qLagrange_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  rw [lhs_eq_Dsum q hq0 n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective_abs q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

end JSP870.Erdos1050
