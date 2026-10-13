# Lean proof of the sharp entropic Rogers–Shephard inequality

The entropic Rogers–Shephard conjecture asks for the following
(see [Melbourne and Tkocz (2020), Conjecture 6.1](https://arxiv.org/html/2005.10930v1#S6)).

> (Conjecture) **Sharp entropic Rogers–Shephard inequality.** Let $`X,X'`$ be independent
> random vectors with the same log-concave probability density on $`\mathbb R^n`$,
> where $`n\ge1`$. Both differential entropies are finite, and
>
> $$h(X-X')-h(X)\le n\log2.$$
>
> The constant is best possible in every dimension. Products of one-sided exponential
> distributions and their invertible affine images attain equality.

This repository contains a complete Lean 4.33.1 proof of this statement,
using FC's pinned Mathlib version. All logarithms are natural.

The two main components are:

1. **A Formal Conjectures style statement.**
   [FClikelean/](FClikelean/) contains two definitions, the main theorem, and a fixed proof link.
2. **The full Lean proof.**
   [Main.lean](lean/EntropicRogersShephard/Main.lean) combines the density inequality,
   finite entropies, the independent difference law, affine equality examples and optimality.
   [FCSolution.lean](lean/FCSolution.lean) connects this proof to the FC-style target.

## Formal Conjectures like targets

### FClikelean

The proposed statement for [FC issue #7196](https://github.com/google-deepmind/formal-conjectures/issues/7196)
is in [EntropicRogersShephard.lean](FClikelean/EntropicRogersShephard.lean).
Only probability density and log-concavity need new definitions. The difference density
is a local integral, and entropy is written directly as the integral of $`-f\log f`$.
The proof link is fixed to the Lean 4.33.1 proof commit that passed private CI.

### Comparator target

[Challenge.lean](lean/Challenge.lean) supplies the reference statements, and
[FCSolution.lean](lean/FCSolution.lean) proves them. The primary target is
`EntropicRogersShephardFC.entropic_rogers_shephard`; four supporting targets cover the
density bound, affine transport, equality examples and optimality.
The [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md) identifies each
natural-language clause and its formal statement.

## Mathematical explanation (AI generated)

Write $`H_k=\sum_{j=1}^k1/j`$ and $`F(k)=k(H_{2k}-H_k)`$.

**1. Control uniform convex bodies.** Brunn–Minkowski gives a radial inequality for
the root of the overlap density. Its level-volume ratio and logarithmic moment yield,
for independent uniform vectors on an $`N`$-dimensional convex body,

```math
h(Z-Z')-h(Z)\le F(N).
```

**2. Compute simplex fibers.** For independent uniform vectors $`U,V`$ on the standard
$`m`$-simplex, explicit difference densities and integer Beta-log moments give

```math
h(aU-bV)\ge h(U-V)+\frac m2(\log a+\log b),\qquad a,b>0,
\qquad h(U-V)-h(U)=F(m).
```

**3. Lift a concave power.** A density proportional to $`\rho^m`$ on a convex body,
with $`\rho`$ upper semicontinuous and concave and $`0<c\le\rho\le C`$, is a marginal of
the uniform distribution on

```math
B_\rho=\{(x,y):x\in K,\ y_i\ge0,\ \textstyle\sum_i y_i\le\rho(x)\}.
```

The explicit mixture of simplex-difference densities and entropy concavity then give
$`h(X-X')-h(X)\le F(n+m)-F(m)`$.

**4. Pass to log-concave densities.** Compact concave-power approximations and common
exponential bounds justify the entropy limits. Since

```math
\lim_{m\to\infty}\bigl(F(n+m)-F(m)\bigr)=n\log2,
```

the result holds for every log-concave probability density. Entropy integrability and
tail bounds are proved from the density assumptions.

**5. Establish sharpness.** The difference of two independent unit exponential variables
has the Laplace density $`e^{-|t|}/2`$. Their entropies are $`1`$ and $`1+\log2`$.
Products therefore attain $`n\log2`$. An invertible affine map adds the same log determinant
to both entropies, preserving their difference.

The [proof note](PDF/entropic-rogers-shephard.pdf) gives the paper argument.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.33.1` | Canonical proof, pinned dependencies, Challenge and FCSolution. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.33.1` | The same proof for browsing and building, with Comparator-only files removed. |
| [FClikelean/](FClikelean/) | `v4.33.1` | Minimal proposed FC-style statement; local statement compilation passed. |
| [lean/comparator/](lean/comparator/) | `v4.33.1` | Input pins, source correspondence, verification scripts and guide. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Build, Comparator, axiom audit and fresh kernel replay. |
| [PDF/](PDF/) | — | Proof note and its existing timestamp evidence. |

The 65 common Lean sources in the canonical and supplementary projects are byte-identical.
[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) records the publication candidate and its verification status.

## Verification

### Lean execution results

The full proof and reference build on Lean 4.33.1 and Mathlib v4.33.1.
All 451 audit targets use only `[propext, Classical.choice, Quot.sound]`.
[FCAudit.lean](lean/FCAudit.lean) checks the five FC connections and the complete main theorem.

### Lean Comparator check

The reference, proof, Comparator and Lean4export all use Lean 4.33.1.
Comparator and Lean4export are pinned to their last 4.33 source revisions;
only their toolchain declarations are changed from 4.33.0 to 4.33.1.
Their Lean source code is unchanged.
The local Comparator CLI passed all five comparisons and its builtin kernel
replay. A separate `leanchecker --fresh FCSolution` replay also passed.
The macOS development check used the upstream sandbox shim.
The private Linux CI run passed with real sandboxing, all five comparisons,
the 451-target axiom audit, and an independent fresh kernel replay.
Public verification is pending. See the
[private CI verification record](lean/verification/private-ci-verification.json) and
[local verification record](lean/verification/local-review-verification.json).

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| 1957 | C. A. Rogers and G. C. Shephard | Established the geometric difference-body inequality underlying the entropy analogue ([geometric background](https://arxiv.org/html/2005.10930v1#S6)). |
| 2015 | Mokshay Madiman and Ioannis Kontoyiannis | Developed the entropic analogue and conjectured the sharp one-dimensional bound, with one-sided exponential extremizers ([Section VIII, Conjecture 1](https://arxiv.org/pdf/1508.04089#page=23)). |
| May 2020 | James Melbourne and Tomasz Tkocz | Stated the all-dimensional Shannon conjecture as Conjecture 6.1 and proved its sharp Rényi analogue for orders $`\alpha\ge2`$ ([Section 6](https://arxiv.org/html/2005.10930v1#S6)). |
| October 2026 | [OpenAI, family 101](https://github.com/openai/math/blob/main/overview.tex) | Presented a proof of the sharp simplex conjecture for isotropic constants and the related entropy lower bound $`h(f)\ge n+\frac{1}{2}\log\det\mathrm{Cov}(f)`$, with affine exponential products as extremizers ([5 October manuscript](https://github.com/openai/math/blob/main/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/introduction.tex)). |
| October 2026 | This repository | Completed a [Lean proof](lean/EntropicRogersShephard/Main.lean) of the sharp Shannon increment bound, including entropy finiteness, the independent difference law, affine exponential equality examples and optimality. |

The OpenAI result bounds entropy from below using covariance. Affine images of exponential
products attain equality in both inequalities. This repository bounds the entropy increase
under an independent difference through the simplex fibers described above.

## Appendix: Verification by Lean Comparator on GitHub CI runner

Comparator checks the theorem statements and dependent definitions against the reference,
audits permitted axioms and replays the solution in the builtin Lean kernel.
A separate job performs a fresh replay of the complete proof environment.

### Certification Within 90 days: CI results

The workflow retains logs and artifacts for 90 days.
[Private Linux CI](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38387993461) passed on Lean 4.33.1
for commit `a4afbe96b42e18434167870dcfd0ba8254bb96de`: build, Comparator, axiom audit
and fresh kernel replay all succeeded. Public CI verification is pending.

### Certification After 90 days: archive

After successful public verification, the original artifact ZIPs, job logs, run
metadata and checksums will be preserved under `ComparatorLogYYYYMMDD/`.

### Reproduce the verification

Build with `cd lean && lake exe cache get && lake build`.
To reproduce the full checks on Linux, run the [verification workflow](.github/workflows/comparator.yml)
in a repository you control. See [the verification guide](lean/comparator/README.md).
