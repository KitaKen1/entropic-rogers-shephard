# A Sharp Entropic Rogers–Shephard Inequality via Simplex Fibers

The entropic Rogers–Shephard inequality asks for the following assertion.

> [!NOTE]
> **Theorem.** Let $`X,X'`$ be independent random vectors with the same log-concave probability density on $`\mathbb R^n`$, where $`n\ge1`$. Both differential entropies are finite, and
>
> $$h(X-X')-h(X)\le n\log2.$$
>
> The constant is best possible in every dimension. Products of one-sided exponential distributions, and their invertible affine images, attain equality.

All logarithms are natural, and $`h`$ denotes differential entropy. This repository presents a proposed proof in the [PDF manuscript](PDF/entropic-rogers-shephard.pdf). A proof sketch follows.

## Proof sketch

Write $`H_k=\sum_{j=1}^k1/j`$ and $`F(k)=k(H_{2k}-H_k)`$.

### 1. Bound the entropy increment for uniform convex bodies

For independent uniform vectors on the same $`N`$-dimensional convex body,

```math
h(Z-Z')-h(Z)\le F(N).
```

Brunn–Minkowski gives a radial inequality for the $`N`$th root of the overlap density. The increasing level-volume ratio and a weighted logarithmic mean give the entropy bound.

### 2. Compare differences of scaled simplices

For independent uniform vectors $`U,V`$ on the standard $`m`$-simplex and all $`a,b>0`$,

```math
h(aU-bV)\ge h(U-V)+\frac m2(\log a+\log b),
\qquad h(U-V)-h(U)=F(m).
```

Compute the density and its level-set volumes. Normalization fixes the coefficients, and integer Beta-log moments give a binomial average of harmonic numbers and the comparison.

### 3. Lift a concave power to a convex body

Let $`\rho`$ be an upper semicontinuous concave function on a convex body $`K\subset\mathbb R^n`$, with $`0<c\le\rho\le C`$. A density proportional to $`\rho^m`$ is the marginal of the uniform distribution on

```math
B_\rho=\{(x,y):x\in K,\ y_i\ge0,\ \textstyle\sum_i y_i\le\rho(x)\}.
```

Entropy concavity for the explicit mixture of simplex-difference densities, combined with the first two steps, yields

```math
h(X-X')-h(X)\le F(n+m)-F(m).
```

### 4. Pass to a log-concave density

Write $`f\propto e^{-V}`$ with $`V\ge0`$ convex. On each fixed compact sublevel set $`\{V\le R\}`$, approximate $`e^{-V}`$ uniformly by $`(1-V/m)^m`$. Since

```math
\lim_{m\to\infty}\bigl(F(n+m)-F(m)\bigr)=n\log2,
```

the bound follows on that sublevel set. Common exponential bounds for the original and difference densities justify entropy convergence as $`R\to\infty`$.

## Lean formalization

An intermediate-results library is being developed in [Lean/](Lean/README.md), with
fixed Lean and Mathlib versions. It includes simplex geometry, finite binomial and
harmonic estimates, integer log moments, and entropy convergence tools. The
simplex overlap formula is now connected to a normalized difference density with
finite entropy, orthant superlevel volumes, and the exact harmonic entropy formula.
The simplex comparison at all positive scales and the uniform-convex-body entropy
upper bound are proved. The original simplex-fiber volume, marginal density and
entropy identity, and the actual lifted-difference mixture formula are also proved.
The mixture entropy comparison and cancellation remain in progress. Positive-support
interior continuity and compact positive density bounds are available for the
general-density limit. The full inequality is not yet formally proved; the remaining
analytic connections and a work estimate are listed in the Lean project README.

## Conclusion

The argument gives $`h(X-X')-h(X)\le n\log2`$ for every log-concave probability density on $`\mathbb R^n`$. For a vector of independent unit exponential variables, the difference density is a product of Laplace densities and the entropy increment equals $`n\log2`$. Thus the constant is sharp.
