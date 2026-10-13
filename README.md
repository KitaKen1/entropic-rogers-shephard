# A sharp entropic Rogers–Shephard inequality

> **Theorem.** Let X and X' be independent random vectors with the same log-concave
> probability density on real n-space, n ≥ 1. Both differential entropies are finite, and
>
> $$h(X-X')-h(X)\le n\log 2.$$
>
> The constant is best possible. Products of one-sided exponential distributions and
> all their invertible affine images attain equality. Logarithms are natural.

The canonical Lean proof is [lean/FCSolution.lean](lean/FCSolution.lean), connected to
the [complete main theorem](lean/EntropicRogersShephard/Main.lean). The
[PDF proof note](PDF/entropic-rogers-shephard.pdf) gives the paper argument.

## Files

| Path | Purpose |
|---|---|
| [lean/](lean/) | Canonical proof, fixed dependencies, proposed target and Comparator configuration. |
| [leanWithoutComparator/](leanWithoutComparator/) | The same proof for browsing and building, with Comparator-only files removed. All 65 common Lean sources are byte-identical. |
| [FClikelean/](FClikelean/) | Proposed FC-style target for [issue #7196](https://github.com/google-deepmind/formal-conjectures/issues/7196). |
| [Target correspondence](lean/comparator/TARGET-CORRESPONDENCE.md) | Clause-by-clause match between the natural language and the formal statements. |
| [.github/workflows/](.github/workflows/) | Fresh Linux build, Comparator, axiom audit and fresh kernel replay. |
| [PDF/](PDF/) | Proof note and its existing timestamp evidence. |

## Proof

For uniform convex bodies, Brunn–Minkowski and an overlap-density logarithmic moment
give the entropy increment bound $F(N)=N(H_{2N}-H_N)$.
Explicit scaled-simplex difference densities give the corresponding fiber comparison.
A convex simplex-fiber lift bounds a concave-power density by F(n+m)−F(m).
Compact approximation and exponential tail bounds pass to every log-concave probability
density; the difference of harmonic expressions tends to n log 2.
The explicit exponential-product difference is a product of Laplace densities.
Both entropies shift by the same log determinant under an invertible affine map.

## Verification

The original proof has 445 local theorems and a 446-target axiom audit, including the
imported Brunn–Minkowski theorem. Its mathematical sources are unchanged from
`c34631bc744bf626e8225c6c91d5e13c7b8a0b4f`.
The publication layer adds five target statements and direct proof connections.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The target is a local proposal for the natural-language issue, not an accepted upstream
FC Lean file. The proof uses Lean 4.35.0-rc3 and pinned Mathlib; FC's current Lean 4.33.1
metadata compilation is a separate check and is not claimed here.
Build with `cd lean && lake exe cache get && lake build`.
The supplementary directory has the same default proof entry point and dependencies.

## Conclusion

The formal proof establishes the sharp inequality with entropy finiteness, the actual
independent difference law, the affine exponential equality family and optimality.

## Appendix: verification records

Private and public CI evidence will be linked here after successful verification.
The workflow retains Actions artifacts for 90 days; original artifact ZIPs, full logs,
GitHub run metadata and checksums will also be preserved in the repository.
