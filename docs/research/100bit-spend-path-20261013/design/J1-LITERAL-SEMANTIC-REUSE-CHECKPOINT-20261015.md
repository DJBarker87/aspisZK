# J1 literal semantic reuse checkpoint (2026-10-15)

Three focused targets now connect the literal semantic classifier to the older masked-semantic event at each parsed row. Their four successful axiom reports contain only standard axioms. Reader success and absence of literal classifier events remain explicit premises; accepted Rust execution is not established here.

## Verified components

`LiteralC1Prefix.c1At_take_current` proves that adding the current indexed message to the prefix does not change the first-message C1 projection, for every in-range list index. Source SHA-256: `ad315183c6a62c23ea4f5cf9375e96d78310096b437599ce2e0911e924272790`; compiled object SHA-256: `5bfc2d26a6046b8c29c57111b4e80a248d73d80d274f0b920716584d9b49bc62`. Its focused evidence is [lean-literal-c1-prefix](../evidence/lean-literal-c1-prefix-20261015/README.md). The bundle preserves three attempts: two failed dependency-resolution attempts and one successful local attempt. The successful theorem has one `#print axioms` report, `[propext, Classical.choice, Quot.sound]`.

`LiteralSemanticViewComponents.bad_iff_semanticBadZ` proves the semantic-bad predicate equivalence under explicit successful public, C1, semantic-prefix, and current-message readers. It does not establish those reader successes. Source SHA-256: `2542639089387a23506e51b7506df026d657d3a613b8d300924fadfb76d19bdd`; compiled object SHA-256: `03683b5db919dc233f9de878f7efcb80b5448bd5bb910ae1a32c89d6a0390764`. Its focused evidence is [lean-literal-semantic-view-components](../evidence/lean-literal-semantic-view-components-20261015/README.md). The bundle preserves two failed proof-plumbing attempts and one successful local attempt. The successful theorem has one `#print axioms` report, `[propext, Classical.choice, Quot.sound]`.

Together, these two green results account for two successful axiom reports. Their evidence retains the failed attempts and records the exact source/object hashes.

## Local execution caveat

The requested remote NUC path was unavailable for this focused attempt, so the compile used the local `lake env` fallback. The incoming r7/r8 local-check object cache was absent. The successful Components attempt used an isolated overlay plus verified objects from the r11/r12 merge cache; its 350-module import-closure scan and fallback-link inventory are retained. These records do not assert a cold dependency build or one historical compile invocation for every transitive dependency.

The local runs used `-M5000`, a sampled process-group stop threshold of 7 GiB, and a 900-second timeout, without a systemd cgroup. Both successful process measurements report zero swaps; this is not a claim about system-wide swap usage. Components took 106.979 seconds by the runner's measurement, with sampled aggregate process-group RSS of 4,181,920 KiB; `/usr/bin/time -l` reports 4,062,150,656 bytes maximum resident size. C1Prefix took 79.835 seconds by its runner, with sampled process-group RSS of 3,821,328 KiB and `/usr/bin/time -l` maximum resident size of 3,843,702,784 bytes. The sampled values and host `time` values are distinct measurements.

## Additional verified target

`LiteralSemanticNoHit.parseMessage_valid` and `parsed_events_excluded` now compile from source SHA `0f91577221a3480d3d066b4ddf8db86226671a064dc72923c39cab6db616e1de`, object SHA `1aff38a52e94b7aa4618df95bb45cc3b1470fc96e10a4a00896c55268b241a02`. The focused evidence bundle is [lean-literal-semantic-no-hit](../evidence/lean-literal-semantic-no-hit-20261015/README.md). It preserves attempt a (proof-plumbing failure) and b (green). The successful attempt took 63.116 seconds, sampled aggregate process-group RSS 4,579,776 KiB, used zero swap, and printed two standard axiom reports. Its Lean command searched only the isolated object overlay, populated from the verified retained caches described above; its evidence does not claim a cold transitive replay.

## Pending targets

`LiteralSemanticLiftNoHit.lean` (`no_hit_lift`) and `LiteralOpeningFunctionalFacts.lean` (`read_functionals`, `read_semantic_components`) remain unverified by this checkpoint. Their source files contain `#print axioms` commands, but that alone is not compile evidence. No green receipt, object pin, or theorem result for those targets is asserted here. Any subsequent run should use the repository's focused-target workflow and record its own source snapshot, exact receipt, resource data, and axiom output.

The root independently checked 86 bundle checksums, all three current source/object pairs, successful receipt/log agreement, and four standard axiom reports. See [the review record](../evidence/j1-local-semantic-lead-review-20261015.json). The source integration base is `185d576e5`, which includes the reviewed R7/R8 merge; these three targets were compiled before that merge from unchanged source bytes. Source/runtime refinement, commitment recovery, terminal acceptance, adaptive-statement soundness and the complete privacy/extraction arguments remain open.
