import JSP870.Erdos1050.Statement

/-!
# JSP-000870 — irrationality of ∑ 1/(2^n − 3)

Catalog: Is the series of reciprocals of powers of two minus three irrational?
Official statement (Erdős–Graham / erdosproblems.com #1050): `∑_{n ≥ 1} 1/(2ⁿ − 3)`
is irrational. Encoded as a `tsum` over `ℕ` via the reindex `n ↦ n + 1`.

Resolution: Borwein, *On the irrationality of ∑ 1/(qⁿ + r)*, JNT 37 (1991),
specialized to `q = 2, r = −3`. Proof engine ported (Apache 2.0) from
`gotrevor/lean-gallery` (`LeanGallery.NumberTheory.Erdos1050`), original
author Trevor Morris; see `JSP870/Erdos1050/` for the full development.
-/

open scoped Topology
open JSP870.Erdos1050

/-- Headline (JSP-000870): the series `∑_{n ≥ 1} 1/(2ⁿ − 3)`, encoded over `ℕ` by
`n ↦ n + 1`, is irrational. -/
theorem reciprocal_pow2_minus_three_irrational :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) :=
  erdos_1050
