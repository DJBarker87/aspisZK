# Owner-approved combined client bundle (D516)

Base: 19c9611220205ef2aae2d6b435a874555e8f0ac5. Branch: codex/pv-c474-draft-20261029.
This bundle completes owner decisions 1, 6 and 7 on the accepted D474 diagnostics/linux_raw draft. No merge, push, client repin or adoption is performed here. The lead reviews and adopts the final bundle.

## Gate status

Pending combined-source gates: exact feature graph, locked offline Rust 1.94.1 build and binary hash; all three ELF identity checks; existing fixtures and 1,000-pair differential; paired timing against the current shipped client under D359(A); equal-public-shape CT-decoder instruction trace.

The earlier D474 paired medians (-1.01% transfer, -0.70% withdrawal) PASS under the owner's adopted D359(A), evidence class **measured under throttling, paired**. They are historical first-half evidence, not the new combined-client timing gate. OPTIONAL-remove-timing.diff is not applied.

## Scope and retained obligations

N7 changes signing-seed custody at the Rust boundary: exactly 64 raw bytes per public key count, followed by fixed-copy decoding. The unchanged Python preparation parses retained JSON key files; this is not a claim of constant-time Python parsing or whole-loader/signing constant time. The fixture planner constructs witness values internally; no private witness integer is accepted from JSON (D283 inventory). Public snapshot/transaction hex remains public. Validation, OS I/O/errors, V370/V371, E1/E2, L1/L2/L3 and event-retaining RunJoin obligations remain named and open. No headline premise or T field is removed, added or weakened. Privacy target not yet established.

## Feature isolation and gate repairs

The first feature preflight (N73500) caught the second unconditional enabling edge at `crates/aspis-r1-cost-probe/Cargo.toml`, in addition to the direct tool-manifest edge. Cargo features are additive; removing only the tool edge cannot meet item 6. The source edge is now removed in that host-prover dependency manifest (not the root workspace). An explicit audit-only `insecure-spend-fixture` feature gates four fixture helpers and the unchanged simulator module; fixture examples explicitly require it. No simulator body, production arithmetic/prover body or verifier body is edited. `fixture-body-binding.json` and `fixture-feature-sites.json` record the structural binding. Existing extraction results about the simulator keep the identical body with the audit feature selected; no simulator law is weakened.

The actual deployed client graph has no insecure fixture feature. Audit harnesses intentionally enable the two constructor features; profiles and other features match, with all exceptions listed in `harness-parity.json`. Their finite fixture/differential results exercise identical production bodies; they are not whole-client machine-code equivalence. The actual client signing, CT trace, runtime fixture and timing gates execute the fixture-OFF client itself.

N73501 successfully built the final client, then failed at the audit manifest's inherited `default-run` pointing to an absent target. N73502 corrects only that audit manifest and builds the harnesses; the successful client build is not repeated. N73503 failed before any default ELF was produced because native build-script LLVM linkers exceeded TasksMax=64. N73504 replaces it with four-core CPU affinity, unchanged memory/task caps and identical release input. No cap increase or unchanged failed retry occurs.

The 1,000-pair gate reuses and verifies the shipped control's retained 6000–6999 outputs read-only against their prior hashes. Only the combined candidate regenerates those cases; the unchanged full-file comparator checks proofs, public bytes, result records, physical nonce ledgers and four complete ordered oracle streams. This avoids repeating an unchanged baseline regression. Results pending.
