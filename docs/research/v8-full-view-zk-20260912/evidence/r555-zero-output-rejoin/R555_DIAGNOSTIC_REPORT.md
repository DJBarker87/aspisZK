# R555 recipient-zero programmed-oracle source-path diagnostic

This is one fixed-seed diagnostic of the frozen selected R117 host verifier on an isolated source copy. It is **not** a real SHA-256 attack, an alternate-witness impossibility result, a game-admissibility decision, an external transaction/account acceptance result, a probability bound, or a proof of privacy or soundness failure. The oracle output was deliberately programmed.

The fresh isolated source copy was created from `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`, frozen stage revision `6677d5f1310ff7373301fbd79f186278f772e68a`, at `/home/dombarker/project-offloads/aspis-r117-zero-output-rejoin-20261004-a`. The frozen verifier `performance_verifier.rs` and selected `positive_transfer.rs` are byte-identical to R117. The full selected Rust flags were used with SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`, plus the R547 host-only `--cfg v8_semantic_rejoin`; overflow checks were enabled. No selected verifier or positivity relation source was edited.

The run selected only the predeclared `recipient_zero` fixture at seed 1. The selected raw public decoder, explicit typed public validator, and raw transition decoder all accepted the rewritten public statement and transition before oracle programming. The existing private install returned `Domain` because the recipient value cell is zero. The diagnostic producer bypassed only that honest-install refusal by setting the existing inverse cell; `we::extract_checked` then rejected the resulting trace. Existing canonicality and active-row balance assertions passed. The diagnostic uses a synthetic account binding derived from the rewritten public bytes and transition; no external transaction or account wrapper was involved.

The existing genuine-terminal-polynomial semantic fixture asserted `first_boundary_wrong=true`. After round-zero compact absorb, R547's exact memoizing `HashFn` adapter installed one zero output for the next previously unread 33-byte `state || 0x01` preimage. The actual sampler returned `z0=0`. All later fresh inputs used SHA-256; the same immutable memoized result was reused on verifier replay. The diagnostic then built the full C1/C2 commitments, roots, openings, authentication data, and 58,046-byte proof body before invoking the selected verifiers.

Both selected verifier entry points returned `Ok(())` on that body under the same programmed oracle. The memo reported one programmed entry and 16 reads: one prover read, two during `verify_payment`, two during raw-input `verify`, and eleven during retained controls. It recorded 865,282 preimages, 268,729 memo hits, and 1,134,010 total hash calls. All six corrupted-byte checks, truncation, and noncanonical-final-value checks passed. This is acceptance under the deliberately programmed oracle for this source path only.

The proof body is `run-zero-output-seed1/proof-1.bin`; its SHA-256 is `a67aee246e8da19ba250d1ed517dba0c0b520339be40783cef50298e8471b5c8`. The exact 65-byte programmed preimage/output is `run-zero-output-seed1/programmed-entry.bin`, SHA-256 `69d173639143b0df7e95f5a3a411a3e32745c28a85e8a65475f2e103b471aaf1`. Public, transition, and synthetic binding hashes are in `SHA256SUMS`.

Focused release build and the single runtime execution each used an individual systemd user scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Cargo was offline, locked, release, one job. `/usr/bin/time -v` recorded:

| Job | Unit | Exit | Wall time | Peak RSS | Swap |
|---|---|---:|---:|---:|---:|
| Host verifier build | `aspis-v8-semantic-rejoin-build-1791074406-359089` | 0 | 37.79 s | 593,820 KiB | 0 |
| Seed-1 recipient-zero run | `aspis-v8-semantic-rejoin-run-1791074456-360830` | 0 | 7.25 s | 619,688 KiB | 0 |

The complete build and run logs, launch scripts, flags, source snapshots, candidate diff, proof artifacts, and checksums are retained in this directory. The receipt identifies the exact target and source hashes; formal `#print axioms` is not applicable to this runtime diagnostic. No second run, search, benchmark, or other case was attempted.

The first remaining proposition is to connect this one programmed-challenge source path to the actual selected shared-oracle challenge law and then provide a bounded adaptive-attempt/extraction-game interpretation under the relevant resource envelope. This run establishes neither an actual-oracle probability nor any extractor guarantee.
