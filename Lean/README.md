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
| `EntropicRogersShephard/LayerCoefficients.lean` | Binomial expansion and identification of every Beta-weighted coefficient from actual normalization |
| `EntropicRogersShephard/LayerLogMoments.lean` | Continuous logarithmic primitive and the exact logarithmic layer moment |
| `EntropicRogersShephard/SimplexEntropy.lean` | Connection of the logarithmic moment to the actual density entropy at unit smaller scale |
| `EntropicRogersShephard/SimplexScaling.lean` | Haar scale transport, exact harmonic entropy formula, equal-scale increment and all-positive-scale comparison |
| `EntropicRogersShephard/MonotoneTilt.lean` | Oppositely ordered factors have nonpositive covariance, using only three L1 hypotheses |
| `EntropicRogersShephard/ConvexVolume.lean` | Tau Ceti ball-and-point lower bound for the volume of a convex set |
| `EntropicRogersShephard/ConvexExhaustion.lean` | Tau Ceti exhaustion of an open convex set from inside |
| `EntropicRogersShephard/ConvexApproximation.lean` | Compact convex exhaustion of a support a.e.; finite-volume convex sets containing a ball are bounded |

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

Expanding this identity and evaluating integer Beta moments now fixes every
coefficient. If `C_j` denotes the coefficient of `(a-b)^j (b-t)^(m-j)` in `W_m`,
then `C_j m B(m,m-j+1) = choose(m,j) V_m`. No block-volume factorial formula is
needed. The continuous primitive `r^m(-log r + 1/m)` and integer Beta-log moments
give the actual entropy formula for `a ≥ b > 0`:

```math
h(g_{a,b})=m\log a+\log V_m+
  m\left(\sum_{j=0}^m w_j H_{2m-j}-H_m\right),\qquad
w_j=\binom mj(1-b/a)^j(b/a)^{m-j}.
```

Haar scaling recovers every positive scale, and reflection exchanges `a,b`.
The harmonic comparison is therefore connected to the actual entropies:

```math
h(g_{a,b})\ge h(g_{1,1})+\frac m2(\log a+\log b),\qquad
h(g_{1,1})-h(U)=F(m).
```

The inequality holds for all `a,b > 0`; it is strict for ordered unequal scales.
These are simplex statements, not the full log-concave-density theorem.

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

Two convex-geometry proofs are adapted from Tau Ceti commit
`f6d68999ea925d5e176a965434bfcde852d376f3`, with copyright and Apache-2.0 license
retained in `EntropicRogersShephard/NOTICE` and `EntropicRogersShephard/LICENSE`.
The source hashes and changes are in `verification/tauceti-provenance.json`.
They are compiled against this project's fixed Mathlib; Tau Ceti is not a Lake
dependency. Its source snapshot uses a different Mathlib revision.

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
already built Mathlib checkout. The audit covers all 170 intermediate theorems
and the imported Brunn–Minkowski theorem. All 171 depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a new axiom.
All nine dependency commits match the manifest. The source hashes and audit
results are in `verification/axiom-audit.json`, with build results in
`verification/latest-build.json`. Mathlib itself was not rebuilt from source.
The audit script also checks that its target list covers every intermediate
theorem declaration in this project's proof modules.

## Remaining work

1. Connect the density formulas to the difference pushforward of product probability
   measures, for the final probability-variable statement.
2. The simplex-difference entropy formula and all-positive-scale comparison are
   proved. Use them in the fiber calculation below.
3. Prove the convex-body entropy upper bound using Brunn–Minkowski, level sets,
   the logarithmic primitive and the proved monotone-tilt inequality.
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
| 2 | Simplex-difference entropy formula and scale comparison — proved | 0 | 5 |
| 3 | Convex-body entropy upper bound | 12–24 | 4 |
| 4 | Simplex-fiber lift and entropy cancellation | 16–32 | 4 |
| 5 | General log-concave densities and tail limits | 20–44 | 5 |
| 6 | Sharpness, final theorem and audit | 8–16 | 4 |

The remaining total is 62–128 hours, rounded to 65–130; a contingency allowance
gives a planning range of 80–170 hours. At 30 working hours per week, this is
about 3–6 weeks.
Milestones 2 and 3 feed into 4, then 5 and 6. The general-density and tail-limit
connections carry the greatest uncertainty. The next central milestone is 3.

## Conclusion

The actual simplex-difference density is connected to its harmonic entropy formula
and the comparison at every positive pair of scales. Completion still requires the
convex-body upper bound, the fiber lift, general-density limits, sharpness and the
final probability-law connection.
