# Supplementary material — "Certificate complexity of uniform descent for the 3x+1 problem"

Author: Hikaru Wakaura (QuantScape Inc.)
Submission target: Experimental Mathematics. Frozen 2026-09-01.

All scripts are self-contained within this bundle, use exact integer /
exact rational arithmetic for every certified quantity, and print the
quantity they verify. Requirements: Python >= 3.9 (numpy needed only for
`exp9_ridge_ostrowski2.py`); Lean 4 via elan (the toolchain is pinned by
`supplement/lean-toolchain` to `leanprover/lean4:v4.32.2`, core Lean only,
no mathlib).

## Claim -> artifact map

| Paper item | Command (run inside `supplement/`) | Expected output |
|---|---|---|
| Lemma 2.1 (affine form / Terras bijection), climb lemma, rigidity identities, descent for odd n <= 1e6 | `python collatz.py` | "all self-checks passed" |
| Machine verification of the climb lemma (Lemma 4.2) | `elan run --install leanprover/lean4:v4.32.2 lean Barrier.lean` (or `lean Barrier.lean` with the pinned toolchain active) | four theorems, axioms `[propext, Quot.sound]` only |
| Machine verification of the affine identity, remainder bound, collapse lemma (both halves), persistence step (Theorem A') | `elan run --install leanprover/lean4:v4.32.2 lean Collapse.lean` | five theorems, axioms within `[propext, Classical.choice, Quot.sound]`, no sorry |
| Machine verification of the rotation lemma (Theorem B lower bound), integer cross-multiplied form with last-minimum scan | `elan run --install leanprover/lean4:v4.32.2 lean Rotation.lean` | `rotation` + `am_min`/`am_strict`, axioms within `[propext, Classical.choice, Quot.sound]`, no sorry |
| Machine verification of Theorem A itself (abstract certificate systems; injection from climbing classes into deep certificates; no-finite-system corollary; key lemma `odds_mod`) | `elan run --install leanprover/lean4:v4.32.2 lean Counting.lean` | `counting_lower_bound` + `no_finite_system`, axioms within `[propext, Classical.choice, Quot.sound]`, no sorry |
| Machine verification of the Theorem B sandwich ( C(k,e0) <= k c(k) <= (k+1) C(k,e0)) against Mathlib | `cd lean_mathlib && lake exe cache get && lake build` (Lean v4.33.1, Mathlib v4.33.1; downloads the Mathlib cache, ~7 GB) | `CollatzB.theoremB`, axioms within `[propext, Classical.choice, Quot.sound]`, no sorry |
| Machine verification of the combinatorial core of Corollary 6.6 (growth inequality 2^{m(e+1)} <= (3*2^m+1)^e, Terras injectivity on (2^m, 2^{m+1}], count <= sum of binomials) | same Lake project: `CountingCorollary.lean` | `CollatzCount.count_le`, `growth_ineq`, `parityset_injective`; axioms within `[propext, Classical.choice, Quot.sound]`, no sorry |
| Depth-20 certificate system (Sec. 9): generation | `python certtree.py 20` | 4404 certificates, 27328 climbing classes, exact cover |
| Depth-20 system: independent verification | `python verify.py` | "OK — 4404 certificates verified, 27328 unresolved classes at mod 2^20, exact cover confirmed" |
| Theorem B sandwich (k <= 1600), rotation lemma exhaustive check (k <= 16) | `python exp7_gamma_sturmian_cycle.py` | sandwich holds for all k, rotation check passes |
| Theorem C/D numerics: stabilized DP for c(k), two-letter statistic, standard-word matrix recursion (n <= 6), matrix-product formula (k <= 200) | `python exp8_renorm_ostrowski.py` then `python exp9_ridge_ostrowski2.py` | recursion and functional checks pass |
| Theorem F context: max-mean-cycle / LP non-feasibility for bounded syndromes (d <= 10), restricted-graph negative drift | `python exp2_lp_meancycle.py` | all-ones positive self-loop; restricted max mean < 0 |
| Theorem G realization check (w <= 64) | `python exp3_barrier3_and_structure.py` | all-ones windows realized by integer segments |
| Theorem A' checks: adaptive collapse (all n <= 2^20, K = 12), persistence c(k+1) >= c(k) with anchor c(20) = 27328, invalidity witnesses (odd moduli q = 5, 7, 11) | `python exp27_adaptive_barrier.py` | "all adaptive-barrier checks passed" |
| Corollary (counting): exact identity brute force vs c(j)*2^(m-j) (m <= 18), exponent convergence, margin bound B(j) < 2^j (j <= 24) | `python exp28_exceptional_count.py` | "all checks passed", B(j) table |
| Appendix A cycle bound k >= 8,963,457,696 | `python cyclebound.py` | exact-integer reconstruction of the bound |
| Corollary 6.6 (counting): for all n in (2^m, 2^{m+1}] staying >= n for m steps, e >= m*theta_M, and #{n} <= sum_{e >= m theta_M} C(m,e) <= 2^{m H(theta_M)} (m <= 22; at m = 20 the count equals c(20) = 27328) | `python exp32_regression_checks.py` (part 1) | "all regression checks passed" |

## Frozen-artifact hashes (SHA-256)

```
d32a24e4b34eb33a0aa8f01406354ae22ddd65a7329b3d3309197150ad3d78fc  certificates.json
c416508cda41b0df105bae91801d70c37a3e2f65c0251bae1c90683492f4ec7d  Barrier.lean
```

A full manifest is in `SHA256SUMS` (verify with `shasum -a 256 -c SHA256SUMS`).

## Notes

- `verify.py` is deliberately independent of `certtree.py`: it re-derives
  all parity vectors and affine data symbolically and re-checks cover,
  disjointness, and descent from scratch.
- Runtimes on a 2024 laptop: everything under ~2 minutes except
  `exp27_adaptive_barrier.py` (~3 min) and `exp8`/`exp9` (~2-5 min each).
