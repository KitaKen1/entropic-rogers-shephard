# Correspondence with FC issue #7196

The source is the natural-language [issue #7196](https://github.com/google-deepmind/formal-conjectures/issues/7196),
and Conjecture 6.1 of [Melbourne–Tkocz, arXiv v1](https://arxiv.org/html/2005.10930v1#S6).
The FC main tree at `817d8a74e6bcd505ac8407388cc12ac3cfda3d0d` does not contain an entropic
Rogers–Shephard Lean target. `FClikelean/EntropicRogersShephard.lean` is our proposed target.
Comparator verifies its mathematical body on Lean 4.35.0-rc3; this is not a claim of
agreement with an accepted upstream target or compilation on FC's Lean 4.33.1.

| Natural-language clause | Formal statement / definition | Why it corresponds |
|---|---|---|
| Every integer n ≥ 1, on real n-space | `n : ℕ`, `hn : 0 < n`, `Fin n → ℝ` | Coordinates identify real n-space; `volume` is n-dimensional Lebesgue measure. |
| Log-concave probability density | `ProbabilityDensity`, `LogConcave` | Measurable, nonnegative, integrable, mass one; the usual multiplicative inequality, including zeros. No boundedness, regularity or support hypotheses. |
| Independent, identically distributed X and X' | `random_vector_bound`: `HasLaw X (densityMeasure f) P`, same for Y, `IndepFun X Y P` | Arbitrary measurable probability space and common density, not an assumed difference law. |
| Actual density of X−X' | `differenceDensity f s = ∫ x, f x * f (x-s)` and the first conclusion of `random_vector_bound` | The difference law is proved, not assumed. |
| Differential Shannon entropy, natural logs | `entropy f = ∫ x, Real.negMulLog (f x)` | `negMulLog t = −t log t`, with the value zero at t=0. |
| Both entropies finite | Two `Integrable` conclusions of `density_bound` and `random_vector_bound` | Absolute integrability precedes the real-valued inequality; Lean's default value for a divergent integral cannot supply the bound. |
| h(X−X')−h(X) ≤ n log 2 | Last conclusion of `density_bound` / `random_vector_bound` | Exact constant and quantifiers. |
| Exponential products and all invertible affine images attain equality | `affine_exponential_equality` | Explicit unit exponential product, every linear equivalence A, every translation b; probability, log-concavity and finite entropies included. A=identity, b=0 includes the basic example. |
| Affine image means the actual pushforward law | `affine_density_law`, `affineImage` | The inverse determinant formula is proved to describe the measure under x↦Ax+b. |
| The constant is best possible in every dimension | `constant_optimal` | Every universal upper bound C is at least n log 2. |

The equality and affine transport statements also hold at n=0, a harmless strengthening.
No equality classification is asserted: the stated affine family attains equality.
All target definitions import Mathlib only, have no holes, and are independent of the
proof. The five `sorry` terms occur only in the reference Challenge and FC draft.
`FCSolution` imports the definitions and the completed proof, never `Challenge`.

`check-fc-draft.py` removes only the FC import/section metadata and declaration attributes;
the definitions and theorem statements are otherwise exact copies. `check-inputs.py`
checks statement text, fixed SHA-256 pins and byte-identical common proof sources.
Comparator then compares the elaborated declarations and their definition dependencies,
audits permitted axioms and replays the exported solution in the builtin Lean kernel.
