/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #1050 — irrationality of `∑ 1/(2ⁿ − 3)`

Erdős & Graham asked whether `∑_{n} 1/(2ⁿ − 3)` is irrational. The answer is **yes**, by
P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory **37** (1991) 253–259;
cleaner self-contained proof in P. B. Borwein, *On the irrationality of certain series*,
Math. Proc. Camb. Phil. Soc. **112** (1992) 141–146 (free: cecm.sfu.ca/~pborwein/PAPERS/P59.pdf).

Method (no transcendence theory): explicit Padé / rational approximants `pₙ/qₙ` to the series with
integer numerators/denominators and a super-exponential error bound `0 < |qₙ·S − pₙ| → 0`, feeding the
classical integer-approximation irrationality criterion (`Criterion.lean`). The contour integral in the
paper is **avoided** — the approximants are reconstructed as explicit finite sums (`Approximants.lean`).

Problem page: <https://www.erdosproblems.com/1050>.
-/

namespace JSP870.Erdos1050
open scoped BigOperators

/-- The Erdős–Graham series `∑_{n≥0} 1/(2^(n+2) − 3)`.

Index base note: every denominator `2^(n+2) − 3 ≥ 1` is positive, so all terms are well-defined
positive reals. The problem is usually written `∑ 1/(2ⁿ − 3)`; the low terms (`n=0,1` give `−1/2, −1`)
are rational, and **adding/removing finitely many rationals does not change irrationality**, so the
index base is a free, faithfulness-irrelevant choice. We start at `n+2` to keep every term positive. -/
noncomputable def S : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)

/-- The tail series defining `S` is summable: every term `1/(2^(n+2)−3)` is dominated by `2^{-n}`.
(Auto-formalized by Harmonic's Aristotle, ported here and verified axiom-clean.) -/
lemma S_summable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := by
  ring_nf
  exact Summable.of_nonneg_of_le
    (fun n => inv_nonneg.mpr <| by
      nlinarith [show (2 : ℝ) ^ n ≥ 1 by exact one_le_pow₀ (by norm_num)])
    (fun n => by
      rw [inv_le_comm₀] <;> norm_num <;> induction n <;> norm_num [pow_succ'] at * <;> nlinarith)
    summable_geometric_two

/- The headline theorem `erdos_1050 : Irrational S` is proved in `Approximants.lean` (it needs the
proof engine); `Statement.lean` re-exports it as the audit surface. -/

end JSP870.Erdos1050
