# Supplementary material — "The 3-adic mixing rate of the Syracuse random variable"

Author: Hikaru Wakaura (QuantScape Inc.)
Submission target: Experimental Mathematics. Frozen 2026-09-01.
Companion paper: "Certificate complexity of uniform descent for the 3x+1
problem" (separate bundle).

Requirements: Python >= 3.9 with numpy. All certified quantities use exact
integer / exact rational arithmetic or error-tracked computation as stated
in each script's header. Run everything inside `supplement/`
(`exp22`/`exp26` import `exp21`; `exp6` imports `exp5`).

## Claim -> artifact map

| Paper item | Script | What it verifies / computes |
|---|---|---|
| Thm 2.1 (one-dimensionalization): recursion, stationarity, full-frequency scans m <= 15 | `exp4_syracuse_mixing.py`, `exp5_delta_asymptotics.py` | chain vs. full Fourier scan; argmax always a power of 2 |
| Thm 2.1(a) primitive root; exact frequency reduction; monotonicity | `exp6_rigor_base.py` | order computation, one-dimensionalization checks |
| Exponent-lattice recursion, exact lattice values | `exp5b_exact_renorm.py` | g_m(k) recursion to m = 60 (exact) |
| Thm 3.1 (first-passage renormalization identity), verified to 1e-14 | `exp8_renorm_ostrowski.py` | identity audit; |F(d,r)| <= 2^{-r} delta_{d-1} |
| Rescaled window computation to m = 1200; deficit k* = m log2 3 - (7.0 +/- 0.3); rate in [0.0790, 0.0800] | `exp10_discriminate.py`, `exp11_rescaled_window.py` | discrimination data and rescaled lattice |
| Thm 4.1 (weighted contraction): identity min f = 2^{-I0}; weighted-norm data | `exp12_weighted_norm.py` | 50-digit identity check; ||g||_w * 2^{I0 m} ~ m^{-1.1} |
| Capped l^1 functional; contraction audit (399 levels, zero violations) | `exp20_l1_functional.py`, `exp23_R1_R2.py` | one-step inequality audit; chain structure |
| Boundary-layer mechanism: main-term failure, crossing terms | `exp13_lower_bound.py` | rate I0 + 0.0093 for the main term |
| Corner localization (r = 0, d = 5), 9-18 cells, 2^{-1.5r} | `exp14_crossing.py` | contribution-matrix decomposition |
| Pinned bridge amplitude 2^{-I0 m} m^{-1.59}; retention ~ m^{-1.06} | `exp15_pinned_bridge.py` | pinned-cell amplitude to m = 400 |
| Retention profile K(s,m) universality; octave factors in [0.62, 0.95] | `exp16_phase_profile.py` | hybrid DP, m = 80..640 |
| l^4 functional S4', Q -> ~18; collision form; above-line profile | `exp17_Lalpha_Lbeta.py` | full-frequency l^4, wrap profile |
| 4-fold Legendre identity min = 2^{-4I0}; window l^4 rate -> 4 I0 | `exp18_l4_contraction.py` | factorized weighted row sum |
| Wrap budget < 1e-4; correlation length ~ 8 | `exp19_wrap_budget.py` | weighted wrap share; autocorrelation |
| Band rates a(delta) (sharp all-b product DP along Tao's update process) | `exp21_tao_product.py` (`tao_bound_rate`), `exp22_close_chain.py` | measured band rates (sampled at m = 240, 320); constraint-system closure at mu = -0.16, r = 0.0504 at those samples — NOT stable under finer sampling, see exp30 rows (the paper claims only r > 0.045) |
| Lemmas 9.1-9.3 support: run lengths, re-seeding rate 0.2%, entry valuations | `exp24_lemmaC.py`, `exp25_anticoncentration.py` | E[run] = 1.00-1.14; entry nu_2 vs Geom(1/2) |
| Remark after Lemma 9.3 (Lemma A alone): size-biased per-entry valuation in a saturated Lemma-A population | `exp31_lemmaA_sizebias.py` | O(log m) per entry in the saturated model (corrected pair spacing h + log2(1/eps) - 1); total-form bound only |
| Lemma 6.1 + Thm 6.2 (geometric law on cycles): identity exhaustive (m <= 12, sigma <= 6), geometric frequencies | `exp29_cstat_verify.py` | zero mismatches; 0.5000/0.2500/0.1250/0.0625 |
| Thm 10.1 (certified instances on the window, m = 64, 128, 256): error-accounted product bounds U_m(k), window suprema, constraint system with zero margin | `exp30_rigorous_window_bound.py [m]` (rigorous; logs `exp30_m*.log` for m = 64, 96, 128, 160, 192, 256 included); `exp26_certify_instance.py [m]` (original floating-point driver, logs `exp26_m128.log`, `exp26_m256.log`) | window sup <= 2^{-4.97} / 2^{-8.4} / 2^{-15.0}; (mu, r) = (-0.10, 0.0350) / (-0.12, 0.0406) / (-0.14, 0.0457) with positive slack; finer sampling m = 96/160/192 gives mu = -0.11/-0.13/-0.14 (r = 0.0379/0.0432/0.0457): the certified rate plateaus at 0.0457 (Remark 10.2). Scope: scanned window only. |

## Notes

- Section numbers refer to the frozen manuscript in this bundle; each
  script prints the quantities it certifies with its own pass/fail lines.
- Longest runtimes: `exp26_certify_instance.py 256` (~20 min),
  `exp11_rescaled_window.py` and `exp16_phase_profile.py` (~10-30 min);
  everything else minutes or less.
- A full manifest is in `SHA256SUMS` (verify with `shasum -a 256 -c SHA256SUMS`).
