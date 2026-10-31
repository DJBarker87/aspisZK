# D524 minimal user client — context checkpoint, incomplete

Branch `codex/pv-uc-20261029`, base `683e01efee`. This is a continuation checkpoint, not an accepted release. **Privacy target not yet established. No premise removed.** Source remains a proposed client; do not ship, merge, push or repin it. `COMMITS.txt` records the implementation and receipt commits; use `git log --oneline 683e01efee..HEAD` for the complete current range.

The preregistration is `DESIGN.md` (committed before Rust). The unchanged fixture target is `devnet_spend`; the new binary is `user_client`. The latter reads an inherited raw-FD wallet record, derives membership locally from all eight complete public lane leaf sets, constructs the original statement, calls the same `RealR1_client::prove_for_proof_accounts`, and encodes the original publication and settlement instructions. Wire/layout equality has NOT yet passed its required differential. There is no network/RPC implementation. A caller must obtain complete public data non-selectively; per-leaf fetching violates D159.

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

The decoder uses fixed offsets/trip counts; canonicality, amount validation and relation rejection are separate observable operations. Constant-time decoding is a design property awaiting its labelled executable check, not an established whole-loader property. Membership selection still has secret-dependent branches/accesses; whole-client L1/L2/L3 remain open. `mask_audit` is removed from the user output because its witness independence was not established. The fixture harness retains its original output unchanged. User diagnostics retain no error payload and print literal messages. Public hexadecimal encoding now uses explicit nibble conversion. JSON serialization, native I/O and the other formatting associations are not credited through Aeneas.Std's Unit formatting model.

## Validation actually performed

| Required final gate | Current result |
|---|---|
| Three pinned release ELFs | NOT RUN on final source; no crates/programs edits, verified by `source-boundaries.json`. Historical bundle evidence read, not promoted to this gate. |
| 1,000-pair fixture differential, statement/proof-input/instruction bytes | NOT RUN; no wire equivalence claim. |
| Own D359(A) user-vs-shipped paired timing, +10%, 15 s | NOT RUN; pv-c474c combined-client timing not repeated. |
| Labelled CT decoder check | NOT RUN. |
| Charon + ae1-identical Aeneas, compiling Types/Funs, standard axioms | FAIL/INCOMPLETE: Charon has_errors=false; Aeneas fails in `membership::input`. No Types/Funs compilation, Lean audit or final replay. |
| Final client SHA and recipe | Final build pending. Exact recipe below. |
| Fixture harness source/build preservation | Source byte-equal to base, hashes in `source-boundaries.json`; Rust 1.94.1 optimized build passed in N75121. No fresh harness binary identity with the earlier bundle artifact is asserted. |

**Focused functional preflight N75121 passed:** actual user-client transfer and withdrawal, fixture-secret records through inherited pipes, complete public leaves, full native proof generation, exits 0 and empty stderr. `preflight-results.json` and N75121 record this finite check. This used source `c66c24afb8…` before subsequent extraction-driven changes. It is not the final differential, acceptance under SBF, a universal correctness theorem, or a current-source timing measurement.

N75121's intermediate user executable: SHA `7ea8cb77a228840f53e980fcdf3e0b498f1d4d152f0b7824dbe274a8c814ab0f`, 2,027,312 bytes. **Not the final candidate SHA.** Its freshly built fixture executable is SHA `6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194`, 2,281,544 bytes. Earlier bundle artifact SHA `da36d6aa…` remains historical. Root workspace, locks, fixture source, crates and programs are unchanged.

## Extraction identity, repairs and remaining refusal

The pipeline verifies Charon SHA `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8` and Aeneas SHA `fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68` before use. The latter is pv-cx2's accepted **functionally identical rebuild (ae1-2)**, not an exact historical-binary match. Its report and three pinned-output comparison results were read from `codex/pv-cx-20261029:evidence/pv-cx2-20261029/REPORT.md`. Neither translator nor generated semantics was edited. Charon uses its pinned nightly; deployed compilation is Rust 1.94.1; compiler preservation remains V370.

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

**Latest N75130/31:** `Not_found` at `InterpReduceCollapse.collapse_ctx_following_sequence`, line 1991, during `user_client::membership::input`. N75131 changes only diagnostic logging (`-log Translate`) to locate the declaration, reusing the same LLBC; it is not an unchanged proof replay and earns no proof credit. The diagnostic shows `main`, `run`, `plan::prove`, and `wallet::read` were visited before the failing membership declaration; this is not a complete translation claim. N75131 exits 2, wall 15.00 s, peak process RSS 2,728,480 KiB, swap 0. No generated file is edited or installed.

Opaque local boundaries now include startup hook installation, public JSON projections, private-directory creation, path joining and public hash-pointer selection, in addition to Accounts::parse and external library operations. Their native source is retained; they are **unproved source-association obligations**, not discharged facts or new T fields. No standard-axioms claim can be made by filling external templates with axioms or sorry. Full source refinement also requires D188 mutable-write/restoration checks once emissions exist. Do not call this extraction gate green merely because remaining failures can be hidden behind opacity.

## Recipe and accounting

`tools/r1-cost-probe/build-client.sh` runs:

```sh
unset CARGO_ENCODED_RUSTFLAGS CARGO_PROFILE_CLIENT_PANIC RUSTC_BOOTSTRAP
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cargo +1.94.1 build --profile client --locked --offline -j 4 \
  --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin user_client
```

Client profile is optimized and panic=abort. Final executable hash must be collected after final source freeze; no shipping pin is changed.

**32/50 native scopes spent**, IDs N75100–N75131 inclusive; **18 remain**, next N75132. **0/40 Lean attempts**, next 75000; **0 Kani**. Host/local receipt inventory and all done statuses agree (`host-checkpoint.json`). All scopes sequential, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; no cap raised. Per-scope receipts record target, exit, wall, peak process RSS, swaps and source revision; #print axioms is N/A for native/extraction. No full Lean regression or successful final acceptance gate was repeated. Expired QUIET_WINDOW marker retained unchanged; its until value and current epoch are in the host checkpoint. The old referenced `r1p-common.txt` is absent at the prompt path; pv-common, local-lean, root AGENTS and the established wrapper were used without changing infrastructure.

Resume recovery: first git status showed only uncommitted N75111 evidence; receipt verified and committed as `36e94b4b54`. Host showed N75111 done with exit 2 and no live task scope. No stopped-session work was duplicated. The final checkpoint again shows only init.scope, all 32 done statuses present. Keys/recovery data/nonce ledgers retained; deployment authority directory never accessed; no RPC, devnet access, broadcast, key cleanup, merge, push or repin.

No assumption in `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` was removed, changed or weakened; its before/after statement is identical. No T field added. E1/E2, V370/V371, RunJoin, full L1/L2/L3, native-I/O/diagnostic associations and shipping adoption remain. The new opaque helper associations above are explicitly open P obligations. **Next deliverable:** split `membership::input` into small source helpers to isolate the branch-join failure, finish faithful extraction and compile/audit it, then freeze the source and run each final acceptance gate once. `HANDOFF.md` contains the exact continuation state. Budget remains unspent at this context checkpoint.
