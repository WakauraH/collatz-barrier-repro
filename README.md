# collatz-barrier-repro

Reproduction repository for two companion papers on the quantitative
difficulty of the 3x+1 (Collatz) problem, by Hikaru Wakaura (QuantScape
Inc.):

- **P1** — *Certificate complexity of uniform descent for the 3x+1
  problem* (`papers/paper_P1.pdf`). Proof-complexity lower bounds for the
  congruence-class descent strategy: every correct certificate system
  needs at least c(k) = 2^{H(log_3 2)k + o(k)} certificates of depth > k,
  robustly under disjunctions and adaptive stopping; non-regularity and
  Sturmian structure of the certificate frontier; an unconditional
  power-saving count N^{0.950} of potential counterexamples. Theorem A
  (counting) and Theorem B (the sandwich) are machine-verified in Lean 4 —
  A and the core lemmas in dependency-free core Lean (`p1/*.lean`), B
  against Mathlib (`p1/lean_mathlib/`).
- **P2** — *The 3-adic mixing rate of the Syracuse random variable*
  (`papers/paper_P2.pdf`). Structural theorems reducing the exponential
  decay of Tao's Syracuse Fourier coefficient delta_m to a single
  isolated x2x3-rigidity input; an exact geometric 2-adic law on full
  periods; error-accounted certification of that input on the full
  frequency window at m = 64, 128, 256 (`p2/exp30_*`); certified numerics
  to m = 1200 and the sharp-rate conjecture
  delta_m = Theta(2^{-I_0 m} m^{-c}), I_0 = (1-H(theta))/theta.

## Layout

```
papers/   frozen manuscripts (tex + pdf)
p1/       one self-contained artifact per computational claim of P1:
          Barrier/Collapse/Rotation/Counting.lean (core Lean, pinned
          toolchain v4.32.2), certificate JSON, independent verifier,
          exact-arithmetic scripts — see p1/README.md
p1/lean_mathlib/   Lake project (Lean v4.33.1 + Mathlib v4.33.1) with
          TheoremB.lean; run `lake exe cache get && lake build`
p2/       same for P2 (exponent-lattice computations, audits, band-rate
          DPs, error-accounted window certification exp30 + logs) — see
          p2/README.md
```

Each `README.md` inside `p1/` and `p2/` contains the full
claim-to-script map with expected outputs.

## Quick start (~2 minutes)

```
pip install numpy
./run_quick_checks.sh
```

This runs the fast end-to-end checks: the P1 foundation self-tests, the
independent verification of the depth-20 certificate system (4404
certificates, exact cover), the adaptive-barrier and counting checks, and
the exact 2-adic cycle-law verification for P2. The Lean check
(`p1/Barrier.lean`) additionally requires [elan](https://github.com/leanprover/elan);
the toolchain is pinned by `p1/lean-toolchain` to `leanprover/lean4:v4.32.2`
(core Lean only, no mathlib):

```
cd p1 && elan run --install leanprover/lean4:v4.32.2 lean Barrier.lean
```

Expected: four theorems, axioms `[propext, Quot.sound]` only. The same
command checks `Collapse.lean`, `Rotation.lean`, and `Counting.lean`
(standard axioms only, no `sorry`).

## Integrity

`SHA256SUMS` at the root covers every file; verify with
`shasum -a 256 -c SHA256SUMS`. The hashes of the two frozen artifacts
quoted inside P1 (`certificates.json`, `Barrier.lean`) match this
manifest.

## Requirements

Python >= 3.9; numpy (P2 scripts and two P1 scripts); elan/Lean 4 for the
machine-verified lemma only. All certified quantities use exact integer or
exact rational arithmetic; the certification drivers state their
remaining float -> interval caveat in the papers.

## License and citation

Code and data are released under the MIT License (see `LICENSE`). To cite,
see `CITATION.cff`; please cite the papers for the mathematical results.
