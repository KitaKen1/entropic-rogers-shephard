# Correspondence with FC issue #7196

The source is the natural-language [issue #7196](https://github.com/google-deepmind/formal-conjectures/issues/7196),
and Conjecture 6.1 of [Melbourne–Tkocz, arXiv v1](https://arxiv.org/html/2005.10930v1#S6).
`FClikelean/EntropicRogersShephard.lean` is our proposed target for the issue;
agreement with an accepted upstream Lean target is not claimed.
The FC proposal has two definitions and one theorem, `entropic_rogers_shephard`.
The Comparator reference includes that main theorem and four supporting targets.
The FC-style statement and full proof compile locally on Lean 4.33.1 with FC's
pinned Mathlib version. Both checker tools build with Lean 4.33.1, and the local
Comparator CLI passed the five comparisons and builtin kernel replay.
A new private CI run with Linux sandboxing is pending the owner's review.

| Natural-language clause | Formal statement / definition | Why it corresponds |
|---|---|---|
| Every integer n ≥ 1, on real n-space | `n : ℕ`, `hn : 0 < n`, `Fin n → ℝ` | Coordinates identify real n-space; `volume` is n-dimensional Lebesgue measure. |
| Log-concave probability density | `ProbabilityDensity`, `LogConcave` | Measurable, nonnegative, integrable, mass one; the usual multiplicative inequality, including zeros. No boundedness, regularity or support hypotheses. |
| Independent, identically distributed X and X' | `entropic_rogers_shephard`: both `HasLaw` hypotheses use the explicit `volume.withDensity` measure, with `IndepFun X Y P` | Arbitrary measurable probability space and common density, not an assumed difference law. |
| Actual density of X−X' | Local `g s = ∫ x, f x * f (x-s)` and the first conclusion of `entropic_rogers_shephard` | The difference law is proved, not assumed. |
| Differential Shannon entropy, natural logs | Direct integrals of `Real.negMulLog (f x)` and `Real.negMulLog (g s)` | `negMulLog t = −t log t`, with the value zero at t=0. |
| Both entropies finite | Two `Integrable` conclusions of `entropic_rogers_shephard` | Absolute integrability precedes the real-valued inequality; Lean's default value for a divergent integral cannot supply the bound. |
| h(X−X')−h(X) ≤ n log 2 | Last conclusion of `entropic_rogers_shephard` | Exact constant and quantifiers. |
| Exponential products and all invertible affine images attain equality | `affine_exponential_equality` | Explicit unit exponential product, every linear equivalence A, every translation b; probability, log-concavity and finite entropies included. A=identity, b=0 includes the basic example. |
| Affine image means the actual pushforward law | `affine_density_law`, `affineImage` | The inverse determinant formula is proved to describe the measure under x↦Ax+b. |
| The constant is best possible in every dimension | `constant_optimal` | Every universal upper bound C is at least n log 2. |

The equality and affine transport statements also hold at n=0, a harmless strengthening.
No equality classification is asserted: the stated affine family attains equality.
All target definitions import Mathlib only, have no holes, and are independent of the
proof. The reference Challenge has five theorem holes; the minimal FC draft has one.
`FCSolution` imports the definitions and the completed proof, never `Challenge`.

`check-fc-draft.py` removes FC import/section metadata, declaration attributes and comments,
then checks the two definitions and main statement against the canonical reference.
The four supporting comparison targets stay in `lean/`. `check-inputs.py`
checks statement text, fixed SHA-256 pins and byte-identical common proof sources.
Comparator then compares the elaborated declarations and their definition dependencies,
audits permitted axioms and replays the exported solution in the builtin Lean kernel.
