import Mathlib

/-!
# JSP-000870 — irrationality of ∑ 1/(2^n − 3)

Catalog: Is the series of reciprocals of powers of two minus three irrational?
Literature: Erdős; Borwein (Bo91) On the irrationality of ∑(1/(q^n+r)).

Fix indexing so the series is well-defined (avoid poles) and prove irrationality.
-/

open scoped Topology

/-- Headline: the reciprocal series ∑ 1/(2^n − 3) (exact index set as in catalog/Bo91) is irrational. -/
theorem reciprocal_pow2_minus_three_irrational :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := by
  sorry
