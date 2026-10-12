# Lean formalization

This project formalizes intermediate results for the proposed proof in the PDF.
The full sharp entropic Rogers–Shephard inequality is still in progress.
`SharpEntropicRogersShephard` states the density-form target, including entropy
integrability as a conclusion. It is a proposition definition, not a proved theorem.

The implementation uses Lean `4.35.0-rc3` and Mathlib commit
`f6090c7095e1e56b3464c1daba5f24631f1290d2`.

## Proof sections

The initial geometric and integral ingredients are in `EntropicRogersShephard.lean`,
divided into the following sections. The density connections are in two extension
modules which reuse that compiled module during development builds.

| Section | Content |
| --- | --- |
| `Scalar` | Reciprocal bound, logarithm bound, quantitative scale gap |
| `Simplex` | Compact coordinate simplices, exact translated intersection, overlap superlevels |
| `SimplexVolume` | Scaling of simplex volume and the overlap-radius volume formula |
| `Binomial` | Finite binomial normalization, first moment, second factorial moment |
| `Vandermonde` | Coefficient identity for the overlap level-volume polynomial |
| `Harmonic` | Uniform harmonic-drop estimate and finite binomial scale-gap bound |
| `ScaleComparison` | The harmonic-average comparison for ordered positive scales |
| `CoefficientLimit` | The limit `F(m+n) - F(m) → n log 2` |
| `LogMoments` | Direct evaluation of integer power-log integrals |
| `BetaLog` | Integer Beta and Beta-log moments by finite recurrences |
| `Entropy` | Entropy integrability and convergence on bounded supports; mixture concavity |
| `PowerApproximation` | Integer-power approximation to the exponential |
| `FiberBody` | Convexity of a body with concave simplex fibers |
| `BodyOverlap` | Compact overlaps and the geometric inclusion used with Brunn–Minkowski |
| `Statement` | Full density-form target with the original generality |

| Extension module | Content |
| --- | --- |
| `EntropicRogersShephard/Density.lean` | Difference-convolution measurability, integrability and normalization; uniform densities; positive simplex volumes; uniform-simplex entropy |
| `EntropicRogersShephard/SimplexDensity.lean` | Pointwise simplex-difference density, normalization, compact support and finite entropy; coefficient uniqueness from a polynomial normalization identity |

`EntropicRogersShephard/Audit.lean` records axiom dependencies of the proved
intermediate results.

For every positive dimension and every positive pair of scales, the actual
normalized simplex-difference density is now proved to be

```math
g_{a,b}(z)=\frac{R_{a,b}(z)^m}{a^m b^m V_m},\qquad \int g_{a,b}=1,
```

where `V_m` is the unit simplex volume. Its entropy is finite, and the uniform
simplex has entropy `m log a + log V_m`. The unit volume remains symbolic;
positivity follows from an included box, without a factorial volume calculation.

The level-volume polynomial still needs to be derived from orthant geometry.
`layer_coefficients_forced_by_normalization` proves coefficient uniqueness **given**
the resulting layer-cake identity; that analytic identity is not yet proved.
The actual simplex-difference entropy has not yet been identified with the
harmonic formula, so the harmonic-average comparison remains an intermediate result.

## Build

From this directory:

```sh
lake exe cache get
lake build
lake env lean EntropicRogersShephard/Audit.lean
```

The `LeanPool/Isoperimetric` dependency consists of three unchanged modules from
Lean Pool. Their source commit, original copyright notices, and Apache 2.0 license
are recorded in `LeanPool/NOTICE` and `LeanPool/LICENSE`.

For development against an existing, already built Mathlib checkout, the local
runner compiles only this project's modules and reads the external cache:

```sh
python3 scripts/build_with_cache.py --mathlib /absolute/path/to/mathlib --lean lean
```

Add `--incremental` to reuse unchanged local modules. The external Mathlib checkout
must match the pinned commit and toolchain. This runner does not rebuild Mathlib
from source. Compilation logs and source hashes are saved in `verification/`.

## Validation

The public proof file and its audit compiled successfully against the pinned,
already built Mathlib checkout. The audit covers all 99 intermediate theorems
and the imported Brunn–Minkowski theorem. All 100 depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a new axiom.
All nine dependency commits match the manifest. The source hashes and audit
results are in `verification/axiom-audit.json`, with build results in
`verification/latest-build.json`. Mathlib itself was not rebuilt from source.
The audit script also checks that its target list covers every intermediate
theorem declaration in this project's proof modules.

## Remaining work

1. Connect the density formulas to the difference pushforward of product probability
   measures, for the final probability-variable statement.
2. Integrate the simplex overlap superlevels over coordinate orthants and identify
   the difference entropy with the finite harmonic formula.
3. Prove the convex-body entropy upper bound using Brunn–Minkowski and level sets.
4. Connect the simplex-fiber mixture calculation to the entropy increment.
5. Normalize the power approximations, control convolution limits and exponential
   tails, and pass to general log-concave densities.
6. Prove sharpness for exponential products and their invertible affine images.

## Remaining-work roadmap

These are estimated working hours for an implementer experienced in Lean measure
theory with AI assistance, including implementation, repairs and verification.
They are not a prediction of automatic execution time. Updated 2026-10-12.

| Order | Milestone | Remaining hours | Difficulty (1–5) |
| --- | --- | --- | --- |
| 1 | Density formulas to probability laws | 6–12 | 3 |
| 2 | Orthant superlevels and simplex-difference entropy formula | 18–35 | 5 |
| 3 | Convex-body entropy upper bound | 14–28 | 4 |
| 4 | Simplex-fiber lift and entropy cancellation | 16–32 | 4 |
| 5 | General log-concave densities and tail limits | 22–48 | 5 |
| 6 | Sharpness, final theorem and audit | 8–16 | 4 |

The remaining total is 84–171 hours; a contingency allowance gives a planning
range of 110–220 hours. At 30 working hours per week, this is about 4–8 weeks.
Milestones 2 and 3 feed into 4, then 5 and 6. The general-density and tail-limit
connections carry the greatest uncertainty. The next central milestone is 2.

## Conclusion

The geometric overlap formula now gives an actual normalized difference density
with finite entropy. Completion still requires its harmonic entropy formula, the
convex-body upper bound, the lift and the general-density limits listed above.
