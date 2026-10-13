# Canonical Lean proof

The entry point is [FCSolution.lean](FCSolution.lean), importing the completed
[Main.lean](EntropicRogersShephard/Main.lean). Compatibility edits adapt the proof
to Lean 4.33.1 without changing the mathematical statements.

```
lake exe cache get
lake build
```

Lean 4.33.1 and FC Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are fixed.
[Challenge.lean](Challenge.lean) contains only the five reference theorem holes and imports
standalone Mathlib-based [definitions](FCTargetDefinitions.lean). The proof never imports it.
[comparator.json](comparator.json) lists every comparison target and the three permitted axioms.

The primary FC target, `entropic_rogers_shephard`, and four supporting targets cover the
original density inequality and finite entropies, the independent
difference law, affine density pushforward, all affine exponential equality examples, and
optimality. See [the correspondence table](comparator/TARGET-CORRESPONDENCE.md).

CI builds the proof on a fresh Linux runner. A separate job builds the trusted Challenge
before restoring proof products, executes Comparator in an unprivileged sandbox with
AF_UNIX disabled, checks all target axioms, and requires builtin kernel acceptance.
Another fresh job runs `leanchecker --fresh FCSolution`.

[comparator/shared-proof-sources.json](comparator/shared-proof-sources.json) records all
65 common sources shared byte-for-byte with `leanWithoutComparator/`.
That auxiliary copy omits only the Challenge, FCAudit, Comparator configuration/scripts
and their two library registrations; its definitions and proofs are unchanged.
