# ACCEPTANCE — JSP-000870 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000870

## Exact original question (English)

> Is the series of reciprocals of powers of two minus three irrational?

Accepted resolution: Borwein (Bo91) / related Erdős series results — prove the series is irrational with exact indexing fixed in Lean.

## Required Lean theorem name(s)

| Lean name | Intended statement |
|---|---|
| `reciprocal_pow2_minus_three_irrational` | The series ∑ 1/(2^n − 3) (exact index set) is irrational. |

## Checklist

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit`
- [ ] Headline theorem proved with correct indexing
- [ ] Public repo HEAD full SHA; formalization.yaml / ATTRIBUTION name Yi-111-a
