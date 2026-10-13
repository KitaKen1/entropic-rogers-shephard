# Supplementary copy of the same proof

The canonical verified project is [../lean/](../lean/). This folder is the same proof
for browsing and building, with Comparator-only files removed. All 65 shared Lean
sources, the toolchain and dependency manifest are byte-identical.

```
lake exe cache get
lake build
```

The entry point is [FCSolution.lean](FCSolution.lean), importing
[Main.lean](EntropicRogersShephard/Main.lean). The file correspondence and SHA-256 values
are in [shared-proof-sources.json](../lean/comparator/shared-proof-sources.json).
