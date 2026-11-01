# D524 minimal user client — D540 continuation checkpoint

Branch `codex/pv-uc-20261029`, exact worktree `/Users/dominic/ZK/.worktrees/pv-uc`, base `683e01efee`. **Target not yet established. Rows removed: NONE.** This is an incomplete checkpoint, not a release, adoption or repin. `COMMITS.txt` records the range (the final checkpoint commit can follow its snapshot).

The source split resolves the handoff's `membership::input` branch-join refusal. N75135 emits full-entry Types/Funs using the unchanged Charon and accepted ae1-2 Aeneas. Full-entry Lean compilation and the standard-axioms gate remain OPEN: the generated external templates have **25 type axioms and 119 function axioms**, inventoried in `external-boundaries.json`. They were retained as templates, never installed, filled with stand-ins, or credited. No new T field, simulator change, observer restriction or premise removal is claimed.

## Current gate packet

| Gate | Result and evidence |
|---|---|
| Three final-source ELFs | PASS against all three SHA pins, N75137/38/39; `final-gates/elf-{default,devnet,pool}/{command,comparison}.json`. Existing stack-size diagnostics retained in receipts; builds exited 0. |
| Final optimized client build | PASS N75136; `final-build.json`; Rust 1.94.1, locked/offline client profile, linux_raw, ct-host-prover. Candidate SHA `9310ca5e3dcb3b2e8d7ac51312d6737aa465d2f8321fdaef6928114ffa38538e`, 2,029,480 bytes. This is a proposed artifact, not a shipping pin. |
| Fixture target | Unchanged source; final build SHA `6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194`, identical to N75121. No equality with the historical bundle's different binary is asserted. SDK target builds at its original dependency pins. |
| 1,000-pair statement/proof-input/instruction differential | **RUNNING N75145; not a pass.** `native75145/pending-status.json` / `host-checkpoint.json` record the snapshot. Audit copies run the complete prover, with no stubs. One additive call immediately before the unchanged RealR1 call captures every compiled-input field as fixed binary data, never Debug. Fresh public nonce labels are identical within each pair. The unchanged comparator requires statement.bin, proof-input.bin and all output/instruction fields equal, except the pre-registered removed mask_audit and separately measured timing. Random proof-byte equality is not claimed. Build/source-copy hashes: `final-gates/audit-build-fixed.json`. |
| Own D359(A) user-vs-shipped timing | **INVALID/INCOMPLETE N75143.** Shipped baseline `30d883a8…` verified. A foreign NEE_K051 Kani scope appeared during the first pair; post-sample quiet check failed, so no complete paired sample or ratio was accepted. `final-gates/timing/*quiet.json` identifies the interfering scope. Expired shared marker preserved; normal admission under e'. Any fresh run needs a recorded changed quiet environment and fresh output path, never overwriting this failure. No pv-c474c combined timing was repeated. |
| Labelled decoder check | PASS N75140, **instruction-trace comparison**. Zero, ff and ramp 212-byte records follow identical 63 instructions, including libc memcpy tail-call; all decoded fields and retained bytes are checked. `final-gates/decoder/ct-decoding.json`, disassembly. Only decoder slice; V371 and whole-client timing/access remain open. |
| Charon/Aeneas full-entry emission | PASS N75135, `extraction75135/`; Charon has_errors=false. Compiling full-entry Types/Funs, standard axioms and final closure replay: **NOT DONE**. |
| D188 source fidelity | Structural inspection retained in `d188-inspection.json`; no lost local array update observed in six listed bodies. Executable emitted-Lean/native checks remain pending, so no blanket D188 pass. |
| Focused decoder extraction | PASS N75144, `decoder-extraction/`; no external templates. Verbatim generated Types/Funs staged as `tools/pv-uc-20261029/lean/PVUCDecoder/`. Compilation/executable check/axioms next, after N75145 is recovered; no concurrent own scope. |
| Final source/artifact audit | PENDING; `source-boundaries.json` verifies fixture identity and no crates/programs edits. No successful gate should be replayed without a covered source/environment/artifact change. |

The differential's expected heavy work is **optimized full proof generation**, not compilation or elimination. It admits at most three prover processes under one 6G/8G/swap0/64-task scope. Per-minute resource/progress records are in its live output; no resource cap was increased. Keep its recovery files, ledgers and compiled cache. Never resubmit N75145 after a transport failure or across a context boundary.

## Private/public boundary

| Input | Visibility | Encoding/location |
|---|---|---|
| Input note nullifier key, salt | Private | 32 + 32 bytes |
| Input note value, asset | Private | u64 LE + u32 LE |
| Change nullifier key, salt | Private | 32 + 32 bytes |
| Recipient owner key, salt, value | Private | 32 + 32 + u64 LE |
| Raw wallet record | Private | Exactly 212 bytes, one inherited FD and EOF; retained in 0600 recovery file in 0700 directory |
| Action, withdrawal amount/destination, transaction/account keys | Public | JSON |
| Lane account bytes, checkpoint, complete eight-lane pair-leaf sets | Public | JSON; supplied independently of selected input note |
| Proof-account candidates, output directory | Public | JSON |

The decoder uses fixed offsets/trip counts; canonicality, amount validation and relation rejection are separate observable operations. The labelled decoder instruction-trace check passed on three fixed-width classes; this establishes neither universal CPU latency nor whole-loader constant time. Membership selection still has secret-dependent branches/accesses; whole-client L1/L2/L3 remain open. `mask_audit` is removed from the user output because its witness independence was not established. The fixture harness retains its original output unchanged. User diagnostics retain no error payload and print literal messages. Public hexadecimal encoding now uses explicit nibble conversion. JSON serialization, native I/O and the other formatting associations are not credited through Aeneas.Std's Unit formatting model.

## Extraction repairs in this continuation

- N75132: split public preparation, roots collection, lane selection, super-root path and final witness construction. All eight complete public lane sets are still scanned, and duplicates/absence/anchor mismatch still reject. The original `membership::input` failure clears; translation reaches `wallet::canonical` and refuses its temporary borrowed digest array.
- N75133: six fixed digest scans replace the nested borrowed-array iteration. Aeneas now refuses the loop's shared-loan collapse at `canonical_digest`. `source-revision-correction.json` records the sparse-add/commit failure: actual submitted bytes are bound by source-inputs hashes and the later matching commit, not by the old HEAD alone. This failed extraction earns no release credit.
- N75134: explicit eight-way bitwise canonicality conjunction clears symbolic translation of all client functions. Emission refuses colliding names for monomorphized core::result::Result instances of the same generic Rust item. This is an internal name-generation collision, not a checked semantic disagreement with another cohort.
- N75135: remove only Charon's monomorphize flag, preserving generic Result types. Full Types/Funs emission succeeds in 21.84 s, 3,456,700 KiB peak process RSS, swap 0. No translator, LLBC or emitted semantics is edited. Existing opacity boundaries remain explicit P obligations.
- N75141: audit-copy build fails only on missing explicit imports of two pair_trace enums. N75142 adds those imports to the audit serializer and rebuilds the same source copies successfully. Final client/fixture/program sources and artifacts do not change.

Charon SHA `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`; Aeneas SHA `fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68`, **functionally identical rebuild (ae1-2)**. pv-cx2's source report and three regeneration comparisons were read. `extraction75135/command.json`, current charon.json and receipt input hashes bind the emission. Extraction uses the pinned nightly, deployed feature selection/profile and Cargo.lock; the standard-library source-parity associations and V370 compiler cohort remain obligations. Metadata records serde_json 1.0.151 and zeroize 1.9.0.

Full-entry generated output is unedited. Its effect/I-O/public JSON/hash selection/formatting/prover external boundaries need faithful models and source association. fmt-1 remains binding; Aeneas.Std Unit formatting does not establish observable writer behavior. Preserving restoration syntax is not an executable D188 validation. No soundness/import-cohort duplicate equivalence is asserted; dup-1' audits remain required if that cone is imported.

Focused Lean tools are prepared, **not executed**: `authority-preflight.py` checks h4 manifest SHA d9187c80… and every selected external object using the h6'' first-root rule. `lean-one.py` compiles one new module under Lean -M7000 and refuses an unchanged failed elaboration source hash. `lean-scope.py` applies the existing admission/barrier and 6G/8G/swap0/64-task caps. Its first expected modules are PVUCDecoder.Types, then PVUCDecoder.Funs. No library objects are rebuilt/substituted and no other stream's objects are written. A generated file without external templates is a useful focused predecessor, not the full-entry gate.

## Earlier refusals retained

Every refusal and exact resource receipt is retained under its native ID; `attempts.json` indexes them. The pre-stall sequence N75100–N75111 is preserved. This continuation fixed or passed beyond:

- N75111: boxed std panic-hook signature; isolated only the literal public startup hook.
- N75112: opaque BacktraceStatus; explicit match and exact enum layout.
- N75113/14: generic borrowed JSON indexing; owned public projection helpers.
- N75115: static-string argument on payload-free Error constructor; zero-argument constructor.
- N75116: opaque range layouts; exact standard ADT layouts exposed.
- N75117: borrowed unwrap returns; owned public text and direct publication-array match.
- N75118/19: opaque domain and lifetime-indexed context layouts; exact reached ADTs exposed, methods external.
- N75120/22: borrowed filesystem builders and generic path join; monomorphic native-I/O helpers.
- N75123/24: opaque hash constant and pointer reification; exact HOST_HASH selection isolated.
- N75125/26: erased reference captured by the actual retry callback; copy public account keys and capture by value. The required RealR1 call remains in the structured plan.
- N75127/28: MaybeUninit from temporary owned JSON arrays; construct vectors by direct pushes.
- N75129: borrowed JSON/iterator payload in membership; own public arrays/text and use indexed loops.

## Recipe, accounting and retained obligations

`final-build.json` records the exact Rust 1.94.1 command with four-core build affinity, `--profile client --locked --offline -j 4`, features `r1p-check,aspis-r1-cost-probe/ct-host-prover`, bins user_client/user_fixture_inputs/devnet_spend, and RUSTFLAGS `--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4`. Client profile inherits release opt-level=3 and panic=abort. The checked-in `build-client.sh` selects only user_client with the same configuration. No target-cpu override, lock or program/source pin is changed. `final-gates/metadata.json` records the complete resolved feature graph.

**46/50 native scopes launched**, N75100–N75145; **45 complete, N75145 pending**, **4 remain**, next **N75146**. **0/40 Lean**, next **75000**; **0 Kani**. `attempts.json` includes pending scopes in spent budget and reserves their IDs. Both wrappers now refuse any existing ID directory. Do not launch another own scope until N75145 completion/status/receipt is reconciled. All completed receipt/resource/admission checks pass in summarize.py; #print axioms is N/A for native work. No formal release audit/replay has run.

All task keys, recovery records, public-fixture SBF keypair files and nonce ledgers are retained. No deployment authority key directory was read/touched, no RPC/network gate/broadcast was used, no key cleanup, merge, push or repin occurred. SSH is transport to the dedicated host only. The missing historical r1p-common.txt remains noted; pv-common through k3/dup-1'/fmt-1/ae1, local-lean and root AGENTS were read again.

No hypothesis of `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` has been removed, added, weakened or changed: before/after endpoint statement is identical. T still has exactly entropy_law, entropy_kernel, observation. E1/E2, V370/V371, RunJoin, native effect/I-O associations and whole-client L1/L2/L3 remain open. **Rows removed: NONE.** Next concrete deliverable: recover the one running 1,000-pair gate, compile/check the focused emitted decoder, discharge faithful full-entry external boundaries and the standard-axioms audit, obtain valid own paired timing under a changed quiet environment, then final source/artifact audit. HANDOFF.md gives recovery details and the remaining budget.
