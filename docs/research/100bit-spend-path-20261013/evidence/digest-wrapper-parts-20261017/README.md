# Digest wrapper source prefix, suffix and retained-model composition

The original sealed candidate's fixed digest prefix is now proved against the retained R0P digest relation. `AspisR1.DigestFixedPrefix.R0PBridge.exactPrefix_success` derives exact source-cut success, canonical eight-cell output, and equality to the original ordered prefix fold from the same actual public value, openings and boxed selector. The source cut retains all checked row arithmetic and the optional recipient presence branch. No intermediate arithmetic/row/binding success or independently supplied public model is assumed. Input digest-word canonical bounds remain explicit and will be supplied by the same-preparation public-field bridge.

`DigestFixedBinding.bindBlock_success` reuses the existing checked selector-row proof and complete eight-lane binding proof. `DigestFixedPrefixSource.exactPrefix_eq_factored` proves that factoring the repeated fragment preserves the complete Result, including errors. The exact original straight-line cut and its reversible helper qualification are pinned by a manifest; only `ok digests4` was appended to expose its output.

`AspisR1.DigestWrapperSuffix.R0PBridge.source_success_r0p` proves the bounded-carry candidate's next-root and conditional next-frontier suffix executes successfully and matches the retained original suffix fold. It computes the carry using the already-proved actual extracted helper, derives checked 33+carry and row arithmetic, derives the same next-frontier array read and its canonicality, and preserves the source order (selector row read before next-frontier read). No carry value, intrinsic-result model or intermediate success is assumed. This is the source-level implementation candidate following the committed Rust patch; full modified-crate extraction, release/runtime correspondence and cost remain separate open obligations.

`DigestModelDecomposition.complete_decomposition` proves the original whole digest relation is precisely prefix fold, twenty-level frontier fold, then suffix fold. `frontier_twenty_eq_fold` connects the symbolic twenty-level recursive model to the original List.ofFn frontier fold. These are generic field-level structural proofs; no concrete field normalization or certificate aggregation is performed.

`TerminalDigestPublicLoopSource` is the exact isolated outer-loop token stream after inverse helper/self qualification and whitespace normalization. Its source-only compile does NOT prove loop execution. `TerminalDigestFrontierModel` is its symbolic recursive target. The actual complete twenty-level source-loop execution theorem is still OPEN and is the missing middle needed to close the whole digest wrapper. This bundle does not claim full accepted-spend soundness, privacy, release-artifact correspondence, or a finished 100-bit theorem.

Every focused target exited0 under 4/6 GiB capped NUC scopes, swap disabled, with no dependency rebuild. Theorems report standard axioms only. Exact commands, source/object/import pins, source revisions, wall time, RSS, swaps and axiom reports are retained. No unchanged full regression or full frozen manifest replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `TerminalDigestPublicLoopSource` | 1.815 | 3982744 | 0 |
| `TerminalDigestFrontierModel` | 1.356 | 3264716 | 1 |
| `DigestFixedBinding` | 1.922 | 4028460 | 2 |
| `DigestFixedPrefix` | 1.829 | 4021520 | 3 |
| `DigestFixedPrefixSource` | 1.827 | 4018108 | 1 |
| `DigestModelDecomposition` | 1.894 | 3285584 | 2 |
| `DigestFixedPrefixR0P` | 1.718 | 4019856 | 3 |
| `DigestWrapperSuffix` | 1.927 | 4065612 | 1 |
| `DigestWrapperSuffixR0P` | 1.85 | 4053940 | 2 |
