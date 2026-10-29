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

## Extraction spans for pv-cx

`changed-spans.json` pins each final file hash and exact line spans against both the pre-D474 source (`a9a9781f8a`) and this continuation's requested base (`19c9611220`). In final source coordinates:

| File | Full bundle changed spans versus a9a9781f8a | Additional changes versus 19c9611220 |
|---|---|---|
| `devnet_spend.rs` | 2–6, 14, 17–25, 27–39, 42–44, 49–53 | 14, 27–39, 49–53 |
| `devnet_spend/plan.rs` | 3; deletion at the line-20 boundary; 29, 40, 108, 112, 114, 118, 123 | none |
| `devnet_spend/Client64_accounts.rs` | 2, 20 | none |

`PATCH.diff` contains the entire production bundle versus a9a9781f8a, including the accepted first half. `PATCH.incremental-from-19c9611220.diff` contains only this continuation. Both reverse-apply checks pass against the final tree. `N7-port.diff` records the exact key-loader block differences from the prepared patch; its Python hunk and fixed-copy decoder are unchanged. All other source additions in this evidence directory are gate tools, not production inputs.

## Completed combined-client gates

- **Build/recipe PASS:** Rust 1.94.1 (`e408947bfd200af42db322daf0fadfe7e26d3bd1`, LLVM 21.1.8), locked and offline. `client` inherits release opt-level=3 and uses panic=abort. `client-cargo-tree-features.txt` and the exact one-root `devnet_spend` unit graph show ct-host-prover ON and insecure-spend-fixture OFF. Root workspace unchanged.
- **New client:** SHA-256 `da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0`, 2,281,512 bytes. This is a proposed replacement artifact hash, not a changed shipping pin. See `client-build.json` for the complete recipe and compiler record.
- **All three ELF rebuilds PASS:** default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` (1,563,728 bytes), devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` (1,563,728 bytes), Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` (605,704 bytes). Receipts: N73504/N73505/N73506; `elf-*/comparison.json`. Existing SBF stack-size diagnostics were emitted; each build exited 0 and the pinned output bytes are unchanged.
- **Existing fixtures PASS:** 3/3 client unit tests; fixed-coin transfer and withdrawal proof/public/result/ledger bytes equal their verified controls (`fixed-fixture-comparison.json`). Actual fixture-OFF client proofs accepted by both default and devnet verifier ELFs with the pinned Pool, with matching settlement and duplicate-reservation rejection (`runtime-private/acceptance.json`). These are native fixture checks, not universal refinement proofs.
- **N7 signing PASS:** exact patched Python invoke on public RFC8032 vector 1 yields the same 158-byte transaction as the current shipped control, SHA-256 `44e9ec48d04617ad3467573d95dc25d3797ab6581618959d11cd6eac23c8b41d`. Original test key retained unchanged mode 0600. Short/extra records reject with fixed diagnostics; malformed JSON and panic tests also retain fixed stderr even with backtrace environment variables enabled.
- **CT decoding PASS — evidence class: instruction-trace comparison.** The actual optimized fixture-OFF client decoder executes the same nine instructions for all-zero and all-0xff 64-byte records of equal public shape. PTRACE_SINGLESTEP records identical relative PCs and source/destination pointer offsets through RET, and checks both output copies. Disassembly contains eight fixed-offset MOVUPS loads/stores plus RET, with no data-dependent branch, early exit, length-dependent loop or table index. This is precisely a decoder-slice comparison, not dudect or whole-loader/signing CT; V371 latency, I/O scheduling, keypair consistency validation and Python preparation obligations remain. See `ct-decoding.json` and `decoder-disassembly.txt`.

Exact recipe (run from any directory via this script; full script in PATCH.diff):

```sh
cd tools/r1-cost-probe
unset CARGO_ENCODED_RUSTFLAGS CARGO_PROFILE_CLIENT_PANIC RUSTC_BOOTSTRAP
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cargo +1.94.1 build --profile client --locked --offline -j 4 \
  --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

Production source freeze: `ba39168f67`; subsequent commits add only gate tools and evidence. `expected-sources.json` binds the staged host sources, and final source/artifact rechecks will be recorded without rerunning successful native gates. Per-scope receipts give target, exit, wall, peak RSS, swaps, revision and `#print axioms` = N/A. No Lean or Kani runs occurred.
