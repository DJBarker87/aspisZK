# Byte-oracle program mapping components

This focused bundle preserves three checked Lean components: independent-answer mean invariance under program-label renaming, an injective embedding of canonical padded addresses into byte strings, and restriction of a program to labels satisfying an all-continuations predicate. The restriction theorem is a program equality under `rename`; it does not establish that the current R1 protocol or every reachable adversarial query satisfies that predicate.

The three focused targets compiled on the pinned NUC workspace with `MemoryHigh=4G`, `MemoryMax=6G`, and swap disabled. Their four exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`. Exact per-target resources, sources, receipts, logs, direct-import pins, and object hashes are in `source-manifest.json`. The target-object archive contains only the three target objects. The three direct-import objects are preserved in the separate deterministic `objects/imports-objects.tar.gz` archive; their loose working copies were moved to `/tmp/aspis-r1-retained-loose-objects-20261015/lean-byte-oracle-program-reuse-20261015/objects/`.

This bundle does not prove that the current R1 adversary is represented by the restricted bounded-address program, that label renaming preserves a shared-oracle experiment without injectivity, or any security bound.
