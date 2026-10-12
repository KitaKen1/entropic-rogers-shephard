# Lean formalization

The density-form entropic Rogers–Shephard inequality, including both entropy
integrability conclusions, is proved by
`EntropicRogersShephard.sharp_entropic_rogers_shephard_density` in
[GeneralDensityBound.lean](EntropicRogersShephard/GeneralDensityBound.lean).
It proves the original `SharpEntropicRogersShephard` proposition for every n ≥ 1
and every log-concave probability density, without extra tail or entropy assumptions.

[ProbabilityLaw.lean](EntropicRogersShephard/ProbabilityLaw.lean) connects the actual
difference density to the law of independent random vectors and proves
`sharp_entropic_rogers_shephard_random_vectors`.
[ExponentialSharpness.lean](EntropicRogersShephard/ExponentialSharpness.lean)
proves equality for exponential products in every dimension and optimality of the
constant. The invertible affine equality family and final presentation remain
in progress.

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
| `EntropicRogersShephard/BodyDensity.lean` | Uniform-body difference density, finite entropy, compact support and normalized overlap root |
| `EntropicRogersShephard/RadialOverlap.lean` | Real-volume BM, radial overlap inequality and increasing level-volume ratio |
| `EntropicRogersShephard/WeightedTilt.lean` | Weighted covariance inequality under the original measure, using four L1 hypotheses |
| `EntropicRogersShephard/BodyLayers.lean` | Measurable finite layer volumes and integrability of the Beta-weighted tilt and log tilt |
| `EntropicRogersShephard/BodyMoments.lean` | Real layer-cake identity, power normalization and logarithmic entropy moment |
| `EntropicRogersShephard/BodyEntropyBound.lean` | Actual uniform-convex-body entropy increment bounded by F(n) |
| `EntropicRogersShephard/PowerDensity.lean` | Normalized powers on a finite support, finite entropy and the direct density-log identity |
| `EntropicRogersShephard/BoundedDensity.lean` | Integrable difference slices, pointwise convolution bounds and finite entropy on compact supports |
| `EntropicRogersShephard/FiberVolume.lean` | Measurable and compact simplex-fiber bodies and their actual volume |
| `EntropicRogersShephard/FiberEntropy.lean` | Actual uniform-lift factorization, marginal density and original lift entropy |
| `EntropicRogersShephard/FiberDifference.lean` | Actual lifted difference density as a simplex-difference mixture, by Fubini |
| `EntropicRogersShephard/FiberDifferenceBounds.lean` | Compact difference support, pointwise bounds and finite lifted-difference entropy |
| `EntropicRogersShephard/LogConcavity.lean` | Native log concavity, positive-support interior continuity and compact positive bounds |
| `EntropicRogersShephard/FiberTransport.lean` | Volume-preserving coordinate concatenation and the actual lifted-body entropy upper bound |
| `EntropicRogersShephard/DensityMeasure.lean` | Real densities as measures and normalized difference-slice probability measures |
| `EntropicRogersShephard/BoundedMixture.lean` | Common bounds and finite supports verify entropy-mixture integrability; entropy rescaling |
| `EntropicRogersShephard/MixtureMass.lean` | Integrability and normalization of common-support mixtures |
| `EntropicRogersShephard/SimplexKernel.lean` | Jointly measurable actual simplex-difference family, common support and bound |
| `EntropicRogersShephard/SimplexMixtureEntropy.lean` | Actual simplex-mixture entropy lower bound at every positive scale |
| `EntropicRogersShephard/FiberMixtureRows.lean` | Entropy lower bound for every lifted-difference row, including zero-mass rows |
| `EntropicRogersShephard/FiberCancellation.lean` | Signed log moments are cross-difference convolutions; actual fiber cancellation |
| `EntropicRogersShephard/FiberExtension.lean` | Extend the fiber size by one outside K; actual concave-power entropy increment bound |
| `EntropicRogersShephard/CompactConvergence.lean` | Pointwise difference-density and entropy convergence on a common bounded compact support |
| `EntropicRogersShephard/FiniteSupportLimit.lean` | Dominated mass limits, a positive mass bound after a finite shift, and scalar normalization invariance |
| `EntropicRogersShephard/ConcaveApproximation.lean` | Normalized concave-power approximation to a compact exponential density |
| `EntropicRogersShephard/CompactExponentialBound.lean` | Both finite entropies and the sharp n log 2 bound for compact exponential densities |
| `EntropicRogersShephard/LocalLogConcave.lean` | The sharp bound for normalized compact convex restrictions inside the positive interior |
| `EntropicRogersShephard/GlobalDensityBound.lean` | Bounded positive superlevels and a global density bound via compact midpoint images |
| `EntropicRogersShephard/ExponentialTails.lean` | Ray interpolation and a global exponential envelope derived from log concavity |
| `EntropicRogersShephard/ExponentialIntegrability.lean` | Multidimensional exponential integrability and an integrable entropy envelope |
| `EntropicRogersShephard/ExponentialConvergence.lean` | Exponential difference-density bounds, finite entropies, and dominated entropy limits |
| `EntropicRogersShephard/DominatedConvolution.lean` | Almost-everywhere dominated input convergence implies convolution convergence at every shift |
| `EntropicRogersShephard/CompactRestrictions.lean` | Growing compact restrictions normalized after a finite mass shift and dominated by 2f |
| `EntropicRogersShephard/GeneralDensityBound.lean` | Difference domination by 4g, the outer entropy limit, and the full density-form target |
| `EntropicRogersShephard/ProbabilityLaw.lean` | Independent random-vector difference laws and the general entropy inequality |
| `EntropicRogersShephard/ProductDensity.lean` | Product normalization, log concavity, coordinate moments and entropy additivity, including zero factors |
| `EntropicRogersShephard/ExponentialExample.lean` | The one-sided exponential, its actual Laplace difference density, and both one-dimensional entropies |
| `EntropicRogersShephard/ExponentialSharpness.lean` | Exponential-product equality in every dimension and optimality of the constant |

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

The convex-body step is also proved. For every positive dimension and compact
convex `B` of positive volume,

```math
h(g_B)-h(U_B)\le F(n),\qquad
g_B(z)=\frac{\operatorname{vol}(B\cap(z+B))}{\operatorname{vol}(B)^2}.
```

Brunn–Minkowski supplies the overlap-root inequality along rays toward zero.
Consequently `V(t)/(1-t)^n` increases on `(0,1)`. The weighted pair-difference
inequality bounds its logarithmic mean by the integer Beta-log mean. The real
layer-cake identity connects that comparison to the actual density entropy.
Layer volumes are measured inside the compact difference support before taking
real values, preserving their measurability and finiteness even at nonpositive
levels. Both body entropies are integrable.

For a measurable finite-volume support `K` of positive volume and measurable
`rho`, with `0 < c <= rho <= C` on `K`, let `Z = integral_K rho^m` and
`f = 1_K rho^m / Z`. The normalized power is a probability density with finite
entropy. The actual uniform density `q` on its simplex-fiber lift satisfies

```math
\operatorname{vol}(B_\rho)=V_m Z,\qquad
q(x,y)=f(x)u_{\rho(x)}(y),\qquad \int q(x,y)\,dy=f(x),
```

and the original lift entropy is proved directly:

```math
h(f)=\log Z-m\int f\log\rho,\qquad
h(q)=h(f)+\log V_m+m\int f\log\rho.
```

Product-measure Fubini gives the actual lifted difference density:

```math
G(s,t)=\int f(x)f(x-s)g_{\rho(x),\rho(x-s)}(t)\,dx.
```

When `K` is compact and `rho` is continuous on `K`, the lifted body and difference
support are compact, and both difference entropies are integrable. These facts
complete the fiber calculation. The mixture entropy lower bound is proved row
by row, including zero-mass rows. The two signed logarithmic moments are
ordinary cross-difference convolutions; their total integrals both equal
`integral f log rho`. Coordinate concatenation preserves volume and entropy,
so the body bound applies in dimension n+m. Extending `rho` by one outside `K`
preserves the normalized power density. A general conditional-entropy chain
rule is not needed for this calculation.

The native pointwise log-concavity definition also gives a convex positive set,
concavity of its logarithm, and continuity on its interior. That interior is
nonempty for a probability density and agrees with the positive set almost
everywhere. Every nonempty compact subset of the interior has positive lower
and upper density bounds. Global boundedness and an exponential envelope are now derived from the original hypotheses.

For every compact K of positive volume and measurable `rho`, continuous and
concave on K with `0 < c <= rho <= C` there, the actual normalized-power density
now satisfies

```math
h(g_m)-h(f_m)\le F(n+m)-F(m),\qquad
f_m=\frac{1_K\rho^m}{\int_K\rho^m},\quad m\ge1.
```

Here `g_m(s) = integral_x f_m(x) f_m(x-s)` is the actual difference-convolution density.
The bound also covers fiber sizes with arbitrary values outside K; the extension
by one is used only internally. Both input and difference entropies are finite.
This concave-power step is used in the completed general-density limit below.

For probability densities with a common compact support and common pointwise
bound, pointwise density convergence now gives pointwise difference-convolution
convergence at every shift and convergence of the difference entropies.
The normalized-power limit gives the sharp bound on each compact convex piece
inside the positive interior. Increasing compact restrictions have masses tending
to one. After a finite shift they satisfy f_j ≤ 2f and g_j ≤ 4g. The global
exponential envelopes dominate both entropy integrands, giving their limits and
h(g) − h(f) ≤ n log 2. Both integrability conclusions are derived, not assumed.

The density-with-measure convolution formula and `IndepFun.hasLaw_fun_add` connect
this bound to the actual law of independent random-vector differences. Each real
convolution slice is first proved integrable before converting to ENNReal.


For the explicit product density `f_n = productDensity n oneSidedExponential`,
finite product integration gives its actual difference density as a product of
`unitLaplace(t) = exp(-abs(t))/2`. The scalar mass and first moment integrals give

```math
h(f_n)=n,\qquad h(g_n)=n(1+\log2),\qquad h(g_n)-h(f_n)=n\log2.
```

`sharpness_exponential_product` includes probability normalization, native log
concavity and both entropy integrability conclusions. The theorem
`entropy_increment_constant_optimal` then proves that every uniform bound for
log-concave probability densities in dimension n is at least n log 2.
The affine equality family remains to be connected.

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

Two convex-geometry proofs and the two-sided exponential route are adapted from Tau Ceti commit
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
already built Mathlib checkout. The audit covers all 422 local theorems
and the imported Brunn–Minkowski theorem. All 423 depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a new axiom.
All nine dependency commits match the manifest. The source hashes and audit
results are in `verification/axiom-audit.json`, with build results in
`verification/latest-build.json`. Mathlib itself was not rebuilt from source.
The audit script also checks that its target list covers every intermediate
theorem declaration in this project's proof modules.

## Remaining work

1. Prove entropy-increment invariance under invertible affine transformations,
   and connect the affine images to the equality family.
2. Complete the final statement and correct the outdated root-file comments
   about the density target; rebuild all affected local modules and repeat the
   full axiom audit.

## Remaining-work roadmap

These are estimated working hours for an implementer experienced in Lean measure
theory with AI assistance. They include implementation, repairs and verification;
they are not automatic execution times or a completion guarantee. Updated 2026-10-13.

| Milestone | State | Remaining hours | Difficulty (1–5) |
| --- | --- | --- | --- |
| General-density bound and both finite entropies | Proved | 0 | 5 |
| Independent random-vector difference law | Proved | 0 | 3 |
| Exponential-product equality and optimality in every dimension | Proved | 0 | 4 |
| Invertible affine images of the equality family | Pending | 6–12 | 4 |
| Final statement, comments, rebuild and audit | Pending | 2–4 | 3 |

The remaining estimate is 8–16 working hours, with a planning allowance of
12–24 hours. At 30 working hours per week, allow about one week.
The affine change-of-variables API has been located in Mathlib. The inverse
determinant factor can be defined directly; both entropies acquire the same
logarithmic correction, which cancels from their increment.

## Conclusion

The general-density inequality, finite entropies, independent random-vector law,
exponential-product equality and optimality of n log 2 are proved. The full goal
still includes the invertible affine equality family and final presentation and
verification.
