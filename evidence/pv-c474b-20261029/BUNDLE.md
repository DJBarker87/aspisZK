# Owner-approved combined client bundle (D516)

Base: 19c9611220205ef2aae2d6b435a874555e8f0ac5. Branch: codex/pv-c474-draft-20261029.
This bundle completes owner decisions 1, 6 and 7 on the accepted D474 diagnostics/linux_raw draft. No merge, push, client repin or adoption is performed here. The lead reviews and adopts the final bundle.

## Gate status

Pending combined-source gates: exact feature graph, locked offline Rust 1.94.1 build and binary hash; all three ELF identity checks; existing fixtures and 1,000-pair differential; paired timing against the current shipped client under D359(A); equal-public-shape CT-decoder instruction trace.

The earlier D474 paired medians (-1.01% transfer, -0.70% withdrawal) PASS under the owner's adopted D359(A), evidence class **measured under throttling, paired**. They are historical first-half evidence, not the new combined-client timing gate. OPTIONAL-remove-timing.diff is not applied.

## Scope and retained obligations

N7 changes signing-seed custody at the Rust boundary: exactly 64 raw bytes per public key count, followed by fixed-copy decoding. The unchanged Python preparation parses retained JSON key files; this is not a claim of constant-time Python parsing or whole-loader/signing constant time. The fixture planner constructs witness values internally; no private witness integer is accepted from JSON (D283 inventory). Public snapshot/transaction hex remains public. Validation, OS I/O/errors, V370/V371, E1/E2, L1/L2/L3 and event-retaining RunJoin obligations remain named and open. No headline premise or T field is removed, added or weakened. Privacy target not yet established.
