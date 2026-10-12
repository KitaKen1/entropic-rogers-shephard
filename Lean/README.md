# Lean formalization

This project formalizes intermediate results for the proposed proof in the PDF.
The full sharp entropic Rogers–Shephard inequality is still in progress.
`SharpEntropicRogersShephard` states the density-form target, including entropy
integrability as a conclusion. It is a proposition definition, not a proved theorem.

The implementation uses Lean `4.35.0-rc3` and Mathlib commit
`f6090c7095e1e56b3464c1daba5f24631f1290d2`.

## Proof sections

The initial geometric and integral ingredients are in `EntropicRogersShephard.lean`,
divided into the following sections. The density and level-set connections are
in extension modules which reuse the compiled ingredients during development builds.

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
| `EntropicRogersShephard/OrthantGeometry.lean` | Sign-flip transport, two coordinate-simplex blocks, null intersections between distinct orthants, exact closed-superlevel volumes |
| `EntropicRogersShephard/LayerMoments.lean` | Bounded weighted layer cake and all positive integer radius moments |
| `EntropicRogersShephard/LayerNormalization.lean` | Real superlevel-volume polynomial and its moment normalization from the actual difference density |

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

The closed-superlevel volume is now proved by splitting over all coordinate
orthants. Write `V_S` and `V_{Sᶜ}` for the unit simplex volumes on the two coordinate
blocks. For `0 < t < min(a,b)`,

```math
W_m(a,b,t)=\sum_{S\subseteq\{1,\ldots,m\}}
  V_S V_{S^c}(a-t)^{|S|}(b-t)^{|S^c|}
  =\operatorname{vol}\{z:R_{a,b}(z)\ge t\}.
```

Distinct closed orthants overlap only on null coordinate hyperplanes. The
implementation sums over the coordinate subsets directly, avoiding a permutation
argument to identify each block volume by dimension. Weighted layer cake then
gives the actual moment-normalization identity for every `a ≥ b > 0`, `m ≥ 1`:

```math
\int_0^b W_m(a,b,t)\,m t^{m-1}\,dt = a^m b^m V_m.
```

Binomial expansion of `W_m(1+s,1,t)` and evaluation with the integer Beta formulas
still need to turn this integral identity into the polynomial hypothesis of
`layer_coefficients_forced_by_normalization`. The logarithmic moment and the
actual simplex-difference entropy have not yet been identified with the harmonic
formula, so the harmonic-average comparison remains an intermediate result.

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
already built Mathlib checkout. The audit covers all 130 intermediate theorems
and the imported Brunn–Minkowski theorem. All 131 depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a new axiom.
All nine dependency commits match the manifest. The source hashes and audit
results are in `verification/axiom-audit.json`, with build results in
`verification/latest-build.json`. Mathlib itself was not rebuilt from source.
The audit script also checks that its target list covers every intermediate
theorem declaration in this project's proof modules.

## Remaining work

1. Connect the density formulas to the difference pushforward of product probability
   measures, for the final probability-variable statement.
2. Expand the proved orthant-volume polynomial, identify the coefficients with
   Beta moments, and evaluate the logarithmic moment to obtain the harmonic
   difference-entropy formula.
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
| 2 | Binomial/Beta coefficient extraction and simplex-difference entropy | 14–28 | 5 |
| 3 | Convex-body entropy upper bound | 14–28 | 4 |
| 4 | Simplex-fiber lift and entropy cancellation | 16–32 | 4 |
| 5 | General log-concave densities and tail limits | 22–48 | 5 |
| 6 | Sharpness, final theorem and audit | 8–16 | 4 |

The remaining total is 80–164 hours; a contingency allowance gives a planning
range of 100–210 hours. At 30 working hours per week, this is about 4–7 weeks.
Milestones 2 and 3 feed into 4, then 5 and 6. The general-density and tail-limit
connections carry the greatest uncertainty. The next central milestone is 2.

## Conclusion

The actual difference density is connected to the orthant superlevel volumes and
their normalized integer moment. Completion still requires coefficient extraction,
the harmonic entropy formula, the convex-body upper bound, the lift and the
general-density limits listed above.
