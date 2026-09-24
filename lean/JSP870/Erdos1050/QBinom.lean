/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Gaussian (q-)binomial coefficients — toward Borwein Lemma 2

The denominator polynomial `pₙ(c,q)` of Borwein's Padé approximants is built from Gaussian binomial
coefficients `[n choose k]_q`, and its **integrality** (Lemma 2) rests on the **Cauchy q-binomial
theorem**. mathlib has no q-binomial machinery, so we build the minimum here.

`qBin q n k` is defined by the q-Pascal recurrence, so it is *manifestly* an integer polynomial in
`q` (a `CommRing` element); no division. The Cauchy theorem is the engine that makes `pₙ ∈ ℤ[c,q]`.

This is a prerequisite for discharging the `borwein_integrality` axiom (O1); see `PENDING_WORK.md`.
-/

namespace JSP870.Erdos1050

/-- Gaussian binomial coefficient `[n choose k]_q`, via the q-Pascal recurrence
`[n+1, k+1]_q = q^{k+1}·[n, k+1]_q + [n, k]_q`. Integer-polynomial in `q` by construction. -/
def qBin {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * qBin q n (k + 1) + qBin q n k

@[simp] lemma qBin_zero_right {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n 0 = 1 := by
  cases n <;> rfl

@[simp] lemma qBin_zero_succ {R : Type*} [CommRing R] (q : R) (k : ℕ) : qBin q 0 (k + 1) = 0 := rfl

lemma qBin_succ_succ {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qBin q (n + 1) (k + 1) = q ^ (k + 1) * qBin q n (k + 1) + qBin q n k := rfl

/-- The Gaussian binomial vanishes above the diagonal: `[n,k]_q = 0` for `k > n`. -/
lemma qBin_eq_zero_of_lt {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∀ k, n < k → qBin q n k = 0 := by
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ k => rw [qBin_succ_succ, ih (k + 1) (by omega), ih k (by omega), mul_zero, add_zero]

/-- The Gaussian binomial on the diagonal is `1`: `[n,n]_q = 1`. -/
@[simp] lemma qBin_self {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBin_succ_succ, qBin_eq_zero_of_lt q n (n + 1) (by omega), mul_zero,
      zero_add, ih]

/-- The q-integer: `[n,1]_q = 1 + q + ⋯ + q^{n-1}`. -/
lemma qBin_one {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qBin q n 1 = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp [qBin]
  | succ n ih =>
    rw [show (1 : ℕ) = 0 + 1 from rfl, qBin_succ_succ, qBin_zero_right, ih, pow_one,
      Finset.sum_range_succ', pow_zero, Finset.mul_sum]
    simp [pow_succ, mul_comm]

/-- `qBin` commutes with ring homomorphisms. In particular `qBin (2:ℝ) n k` is the integer
`qBin (2:ℤ) n k` cast to `ℝ` — the bridge that makes Borwein's `pₙ(c,q)` integer-valued at `q = 2`. -/
lemma qBin_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : R) :
    ∀ n k, qBin (f q) n k = f (qBin q n k)
  | _, 0 => by rw [qBin_zero_right, qBin_zero_right, map_one]
  | 0, _ + 1 => by rw [qBin_zero_succ, qBin_zero_succ, map_zero]
  | n + 1, k + 1 => by
      rw [qBin_succ_succ, qBin_succ_succ, qBin_map f q n (k + 1), qBin_map f q n k,
        map_add, map_mul, map_pow]

/-- Triangular-number identity in `ℕ`: `k*(k-1)/2 + k = (k+1)*((k+1)-1)/2`. -/
private lemma cauchy_tri_succ (k : ℕ) :
    k * (k - 1) / 2 + k = (k + 1) * ((k + 1) - 1) / 2 := by
  rcases k with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1 + 1) * (m + 1) = (c + (m + 1)) + (c + (m + 1)) := by
      have : (m + 1 + 1) * (m + 1) = m * (m + 1) + 2 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- Power-level triangular identity: `q^(k(k-1)/2) * q^k = q^((k+1)k/2)`. -/
private lemma cauchy_tri_pow {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    q ^ (k * (k - 1) / 2) * q ^ k = q ^ ((k + 1) * k / 2) := by
  rw [← pow_add]
  congr 1
  have h := cauchy_tri_succ k
  simpa [Nat.add_sub_cancel] using h

/-- **Cauchy q-binomial theorem** (the engine of Borwein Lemma 2):
`∏_{i<n} (1 + q^i·t) = ∑_{k≤n} q^{k(k-1)/2}·[n,k]_q·t^k`.

Borwein's form `∑_{m≤n} y^m q^{m(m+1)/2}[n,m]_q = ∏_{k=1}^n (1+y q^k)` is the `t = q·y` case.
Proved by induction on `n` via the q-Pascal recurrence (Aristotle-formalized, verified axiom-clean
in our kernel). -/
theorem qBin_cauchy {R : Type*} [CommRing R] (q t : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + q ^ i * t)
      = ∑ k ∈ Finset.range (n + 1), q ^ (k * (k - 1) / 2) * qBin q n k * t ^ k := by
  induction n generalizing t with
  | zero => simp [qBin]
  | succ n ih =>
    set P : R := ∑ k ∈ Finset.range (n + 1),
        q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k with hP
    set Q : R := ∑ k ∈ Finset.range (n + 1),
        q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1) with hQ
    have hprod : ∏ i ∈ Finset.range (n + 1), (1 + q ^ i * t) = (1 + t) * P := by
      have ev : (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t)) = P := by
        rw [show (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t))
              = ∏ i ∈ Finset.range n, (1 + q ^ i * (q * t)) from
            Finset.prod_congr rfl (fun i _ => by rw [pow_succ]; ring), ih (q * t), hP]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_pow]; ring
      rw [Finset.prod_range_succ', ev, pow_zero, one_mul]
      ring
    set A : R := ∑ k ∈ Finset.range n,
        q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1) with hA
    have hPA : P = 1 + A := by
      rw [hP, Finset.sum_range_succ', hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      ring
    have hsplit : ∑ k ∈ Finset.range (n + 2),
        q ^ (k * (k - 1) / 2) * qBin q (n + 1) k * t ^ k = P + Q := by
      rw [Finset.sum_range_succ', hPA, hQ, hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      rw [show (∑ k ∈ Finset.range (n + 1),
              q ^ ((k + 1) * k / 2) * (q ^ (k + 1) * qBin q n (k + 1) + qBin q n k)
                * t ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1))
              + (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1)) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)]
      rw [Finset.sum_range_succ, qBin_eq_zero_of_lt q n (n + 1) (Nat.lt_succ_self n)]
      ring
    have htP : t * P = Q := by
      rw [hP, hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show t * (q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k)
            = (q ^ (k * (k - 1) / 2) * q ^ k) * qBin q n k * t ^ (k + 1) by ring, cauchy_tri_pow]
    rw [hprod, hsplit, add_mul, one_mul, htP]

end JSP870.Erdos1050
