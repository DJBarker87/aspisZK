# R547 programmed-oracle diagnostic (not a security proof)

This report records one fixed-seed source diagnostic on an isolated copy of the frozen R117 source. It does not prove a real SHA-256 attack, a probability bound, privacy, extraction impossibility, or a knowledge-soundness break.

The selected-source base is `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`, revision `6677d5f1310ff7373301fbd79f186278f772e68a`. The diagnostic copy is `/home/dombarker/project-offloads/aspis-r117-semantic-rejoin-20261004-a`; the frozen selected source was not edited. The run used the full selected R117 Rust flags (`selected-rustflags.txt`, SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`) plus only `--cfg v8_semantic_rejoin`. `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true` was set. The selected `performance_verifier.rs` was left unchanged and is shared by both verifier entry points with the host `HashFn` adapter.

The diagnostic compiles the legal fixture and ordinary attempt first. It confirms `extract_checked` accepts the normally installed trace. It then changes only masked `trace.c1[0][12]` by adding one, checks the field value remains canonical, and confirms `extract_checked` rejects that changed trace. The public statement, binding, transition, and attempt are not modified. The altered trace is encoded and committed through the selected host path.

The existing literal negative semantic fixture constructs the actual terminal polynomials and asserts `first_boundary_wrong=true`. Immediately after round-zero compact absorb, it arms exactly one zero result for the next fresh preimage of 33 bytes, `state || 0x01`. Arming asserts that preimage has not been read. The actual ordinary sampler then checks `z0=0`. Every other fresh preimage uses SHA-256; every preimage and output is memoized, and verifier replays reuse that exact entry. Later challenges use ordinary SHA outputs. The full PCS, roots, openings, authentication records, and body are constructed before either selected verifier is called.

On the recovery run, both selected verifier entry points returned `Ok(())` for the 58,410-byte body. The current selected verifier executes both its optimized semantic replay and its dense/reference replay, so the two entry points produce four reads of the programmed challenge preimage. The memo recorded one programmed entry; counts were 1 prover read, 2 reads during `verify_payment`, 2 during raw-input `verify`, and 11 additional reads while running the retained corrupted-byte, truncated-body, and noncanonical controls. All controls passed. The memo contained 865,282 distinct concatenated-byte preimages, recorded 268,761 memo hits and 1,134,042 total hash calls. The exact 65-byte programmed entry (`33-byte preimage || 32-byte zero output`) is `recovery-programmed-entry.bin`; its SHA-256 is in `SHA256SUMS`.

The proof body is `recovery-proof-1.bin`. Public statement, transition, and binding artifacts are saved alongside it. Their hashes and the programmed-entry hash match between the first and recovery runs; the first run did not save its body. The run was one fixed seed (`seed=1`), with no seed scan, nonce search, challenge retry, or benchmark.

The first diagnostic execution already produced the same successful verifier outcomes and passed the normal controls, but its evidence assertion incorrectly expected only two challenge reads rather than four. That run exited 101 after the controls and before saving the proof. Its complete log and exact source snapshots are retained as `run-0001-seed1.log` and `run1-*.rs`. The one recovery run changed only instrumentation accounting and moved body persistence before the final assertions; proof construction and challenge schedule were unchanged. No further run was made.

Focused release host-target compilation used offline, locked Cargo with one job and the full selected flags plus the diagnostic cfg. Every build/run ran in its own user systemd unit with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128` unless noted. `/usr/bin/time -v` reported peak RSS and swap. Attempts:

| Attempt | Result | Wall time | Peak RSS | Swap | Detail |
|---|---:|---:|---:|---:|---|
| build 0001 | exit 127 | under 1 s | not measured | not measured | Preflight wrapper missed the Rust toolchain path; no cgroup build began. |
| build 0002 | exit 101 | 27.21 s | 594,348 KiB | 0 | Changed host target exposed one moved-value error in the new adapter. Full log retained. |
| build 0003 | exit 0 | 11.15 s | 549,236 KiB | 0 | First green build for the first diagnostic run. |
| run 0001 | exit 101 | 7.15 s | 620,172 KiB | 0 | Both verifier entry points returned `Ok(())`; ordinary controls passed; instrumentation assertion expected 2 reads but measured 4. |
| build 0004 | exit 0 | 11.52 s | 549,556 KiB | 0 | Green build after instrumentation-only correction. |
| run 0002 | exit 0 | 7.19 s | 620,064 KiB | 0 | Fixed seed 1; full body saved; both verifiers and all retained controls passed. |

Complete logs, launch scripts, source snapshots, source diff against frozen R117, selected flags, generated artifacts, and SHA-256 manifest are saved in this directory. The formal campaign's outstanding privacy and soundness proofs remain open; this programmed-oracle result does not close either one.
