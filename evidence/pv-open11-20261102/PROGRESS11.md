# D571 ranked-row continuation

**No row restored. Endpoint premises removed/added/weakened: 0/0/0. Target not yet established.** Work stayed on `codex/pv-open11-20261102` in the assigned worktree. Proof/input/receipt stage: `aff7e3df5f9fd7e60776ac3cf64f1ccb58e9cd28`. This is an unfinished context checkpoint with budget remaining, not a release result or a privacy counterexample.

## Per-row result

| Row | Result and exact remaining premise |
|---|---|
| V176 | **OPEN, bounded pass ended.** Native `Repr::data`, all four packed tags, valid ErrorKind conversion, provenance-preserving pointer subtraction, both shared field loads and Linux errno decoder still need binding to the borrowed getter in the unchanged borrow/world frame. Then instantiate the SAME `hkind` in `PDict_OwnedErrorTransport.reserve_transport`, changing only op23 on an actual native op3 carrier. No such carrier/load instance was installed. Do not substitute the reference-only Kind carrier or shift this missing work into V268/V271. |
| V181 | **OPEN.** Bind the physical literal69 constructor/name-stage law to adopted native String/header/allocator/world and terminal/diagnostic observation in the same caller frame, with complete reached callers or proved exclusions. The adopted allocator aborts on null *inside* alloc; std does not receive AllocError on that path. Public-sized allocator failure remains under rdea-1; no success premise was added. |
| V178 | **OPEN.** Bind native clone-first Path::join, actual owned String argument, header/world and all success/error/abort prefixes. The inherited `JoinHandlers.finalWorld` releases partial join and owned name on capacity overflow. Adopted panic=abort does not unwind; that consumer cannot be installed unchanged. Either prove overflow unreachable from the existing actual domain or bind the actual hook/abort branch without those releases. Success still releases the owned name. |
| V369 | **OPEN.** CHECK_TIMES declaration/write/read are cfg-disabled in the adopted source; its take function returns Vec::new. The checker call, four Instant/elapsed pairs and QUIET TLS set/reset/hook lookup remain. Bind the selected source, resource/error prefixes and full SAME-cp native ordered observation to the existing trace law. Gating stored durations does not prove the joint law. |
| V267 | **OPEN.** Instantiate op261's complete Result and returned File token in the native post-world: fd provenance/ownership, libc write outcomes, partial offset updates, errno/cvt, Interrupted predicate, static WriteZero error and all prefixes. The source retries Interrupted without a bound. DIAG12's fuelled writeAll is a prefix model; completion/divergence and valid native count bounds remain. Do not replace a slice panic with its model contract-error code or add a fuel bound. |

Exact source checks and hashes: `PV_O11_V176-binding-status.json`, `PV_O11_next-rows.json` (26 checks), `PV_O11_write-all.json` (12 checks), and `PV_O11_adopted-source-pins.json`. Eight relevant project source snapshots match the adopted da36d6aa bundle's `expected-sources.json`; da36d6aa is the client artifact SHA prefix, not a git revision. Source-shape checks are structural inspection evidence, not complete native bindings. E1/E2, actual joint observation, V370, runtime/allocator adequacy and remaining native links stay explicit. T remains exactly entropy_law/entropy_kernel/observation.

## Proved, extracted and audited

N90503 extracts the safe generic shared-reference carrier without a dynamic trait type; N90504 translates it with the unchanged pinned ae1-2 binary. Generated output is retained byte-for-byte. The emitter normalizes the module path to `PVO11Borrowed.{Types,Funs}` while declarations use `PV_O11_Borrowed`. The reference preserves generic Custom payload and SimpleMessage fields; no mutable borrow/write or backward continuation occurs. It is not the native packed Error representation, and its OS decoder remains an explicit parameter.

90404/90405 compile the exact emitted Types/Funs; 90406 proves `PV_O11_BorrowedLaw.complete` and `frame`. Both have empty SUMMARY-BASED axiom lists. 90407 compiles the new audit driver; 90498 performs the NEP importAll/private HARD-ERROR raw walk: 270/276 reachable constants, 1,564/1,623 edges, no unresolved constant, empty walked axioms equal collectAxioms. This audits the reference only, not a native instance, endpoint, frozen manifest or release. No NDR object was loaded. Every external authority object was hash-checked; effective resolution of all5,673 objects was recorded before each of these five Lean scopes.

V176 used seven new scopes plus eight inherited getter scopes, conservatively **15 total**, meeting its bounded-effort limit. No further V176 attempt is authorized under that bound.

## Native attempts and their limits

- **N90505:** direct std String::with_capacity extraction, with alloc/string/vec/raw_vec/alloc and core/alloc included. Charon's process exited0 but `has_errors=true`: `rustc_trait_elaboration/src/item_ref.rs:312:27`, range start index1 out of range for length0, while extracting RawVecInner::try_allocate_in. This LLBC is REJECTED. It was not translated or retried. `receipts/N90505/semantic-status.json` records rejection; own runners now reject unchanged semantically failed inputs even when tool exit is0. No translator was changed.
- **N90506:** exact adopted diagnostics module, native rustc1.94.1, opt3/debug assertions off/overflow checks off. Capacity69 succeeds. Capacity overflow under panic=abort emits `client panic` and does not Drop the stack marker. The deliberately different unwind-profile control does Drop it. The initial OOM probe unexpectedly took its non-null exit23; the overall attempt FAILS and is retained. Its cause was not established, and no OOM evidence is claimed from it.
- **N90507:** changed OOM-only experiment: black-boxed 1GiB request/pointer, 256MiB RLIMIT_AS, core dumps disabled, same exact diagnostic allocator. It aborts with no stderr or Drop marker, as expected. No already-successful N90506 case was rerun. These are finite fixture observations; no whole-client, actual Path::join-overflow witness or witness-dependent privacy failure is established.

Full failed Rust/driver inputs are retained under `failed/`. Unexecuted join extraction/translation inputs are retained as proposed inputs only; no scope or output is attributed to them. The already-failed common allocator extraction is not a reason to repeat it through join.

## Counters, procedural corrections and next work

Cumulative **10/97 Lean**, **8/30 native**, **0 Kani**. Remaining **87 Lean /22 native**. Next development ID **90408**, next native **N90508**; **90499** remains reserved for audit. Numeric ID availability does not enlarge the conservative97 total. All18 cumulative scopes have receipts; every admitted scope was serial, allowed:true/exit0, 6G high/8G max/swap0/Tasks64, Lean-M7000. No cap raise, timeout, memory kill, reservation refusal or unchanged failed resubmission occurred in this continuation. Exact time/RSS/swap/source/command/axiom fields are in `PV_O11_receipt-index.json` and per-scope receipts.

Two procedural corrections are explicit. N90503 inherited a stale host revision.txt label95c8cc2d5f; actual launch HEAD was ce764e00a6 and its exact dirty source SHA is recorded. Later scopes use ce764e00a6 as launch baseline, not an assertion that uncommitted proof inputs were already tracked there. Also the early ID folder scans used the wrong shared sent.txt path and did not successfully read the shared index before launch. A subsequent scan of all three actual shared evidence/sent.txt files found no matching IDs; it is supplementary, not represented as a pre-launch check. N90507 and90407/90498 used the corrected pre-launch paths. Runner snapshots cover every new receipt's guard hash.

`PV_O11_validate.py` checks all18 receipts, both audits, source hashes, exact generated copies, failed-source snapshots and rejected LLBC, standard accepted proof axioms, source gates and artifact limits. No frozen release replay or unchanged runtime/reproducibility suite was rerun. Retained object fingerprints are in `PV_O11_retained-object-hashes-D571.json`; no scope is running, no local target/ exists, no key action occurred. Do not delete the retained host cache.

Continue with ranked **V171**, then V175/V172. Their native Unix open/options/fd/error/world association must be installed into the existing links, with current panic/allocator behavior and the same observer. Preserve live-owned exclusions. No row closure follows from the source census or reference laws above.

## D573 continuation — ranks 6–10

No row restored; endpoint premises removed/added/weakened = **0/0/0**. Ranks 1–5 were not reopened. Each new row received one bounded source/consumer inspection pass, with **zero Lean/native launches**, below the 12-attempt-per-row limit. No unchanged rejected allocator/dynamic-trait extraction was attempted through another wrapper.

### Rank 6 V171 — OPEN

Instantiate the SAME op14/fileOpen typed algebra on the native caller, not a pure world lift. Bind generic P::as_ref and P destruction; new/read-only options; Unix path bytes, stack/heap conversion at 384, allocation-before-NUL-validation, NUL Error and CString zero-store/deallocation; ordered flag validation, open64/errno and unbounded Interrupted retry; fd adoption and complete returned Result with its post-world. Preserve native ownership, cleanup/abort prefixes and the existing sync_directory caller/observer. DIAG12 openRetry is a finite prefix, not completion/divergence. No new success assumption or T field.

### Rank 7 V175 — OPEN

Instantiate the SAME op22/optionsOpen on actual Options and P in the full native world. Path conversion occurs BEFORE access/creation validation. Bind all flag/mode bits (custom i32 masks ACCMODE only), validation Error::new payload/allocation and abort, open64 pointer/mode ABI, errno capture, unbounded EINTR retries, successful FileDesc ownership and all argument/temporary drops. The actual reservation domain is write/create_new/custom0/mode0600, but every other reached caller needs an exclusion or the general branch law. Preserve complete Result/error/world/observer and no fuel bound. Source validation checks alone do not install this link.

### Rank 8 V172 — OPEN

Instantiate the SAME op15/fileSync typed algebra for the actual borrowed fd and native pre/post-world. Bind fsync (Linux, not Apple F_FULLFSYNC), cvt of -1, immediate errno/Error capture, unbounded Interrupted retry, other errors and successful unit return, with the owner preserved during the borrow. The surrounding caller closes the directory File on ordinary return, and the reservation File after its later directory-sync prefix or ordinary error; panic=abort does not unwind. Retain per-attempt resources, failures, blocking/divergence and ordered native observation. No success/fuel premise or new T field.

### Rank 9 V268 — OPEN

Supply the SAME ExternalTypes.op3 native interpretation for all four Error representations, preserving OS code, valid Simple discriminant, static SimpleMessage and entire Custom {kind, Box<dyn Error+Send+Sync>} with its allocation/payload/vtable ownership. Bind constructors, moves, into_data ManuallyDrop, decoding, shared/mutable access, observations and Custom destruction/deallocation exactly once, in the actual world and caller frame. Error::new allocation/abort and errno-based construction remain included. The borrowed reference and a Kind-only quotient do not supply this ownership/type law; no getter reattempt is made. V176 remains the separately recorded pure getter obligation, and neither row is discharged by assigning its missing work to the other. Dynamic payload/drop/formatting associations and reached domains remain explicit.

### Rank 10 V271 — OPEN

Bind std File -> sys File -> FileDesc -> OwnedFd/ValidRawFd to the existing nonnegative I32 value view with a live ownership invariant in the SAME world. A subtype or descriptor roundtrip supplies no live fd authority. Prove successful open transfers the returned live fd once; borrowed I/O never duplicates/releases it; each ordinary scope exit destroys the owner once. Linux Drop issues one close, ignores its result and does NOT retry EINTR. Bind the check_library_ub/debug fcntl/abort gate at the adopted configuration, fd reuse/provenance and all native returned/post-world observations. Abort paths retain their actually performed prefixes without invented stack cleanup. No availability or exactly-once physical-close success assumed.

Validation: `PV_O11_open_sync.py` passes 38 exact source/consumer checks. `PV_O11_io_provenance.py` matches all eight retained std/alloc snapshots to the deployed 1.94.1 host rust-src, including four newly retained helper/owner/CString files. These are source checks, not own-1 complete structural bindings or native installations. Original typed algebra/caller and prefix-model sources are retained under `inputs/io/`. The `CString` slice specialization allocates/copies before checking NUL; its later destruction first zeros byte0 then destroys its boxed slice. `OwnedFd` destruction has the source `check_library_ub` gate before its single close; its compiled setting is not silently inferred from the client profile.

Counters unchanged: **10/97 Lean, 8/30 native, 0 Kani**; remaining **87/22**, next IDs **90408/N90508**, reserved audit **90499**. No scope running. Next rank **11 V239**, then V249/V269/V403. All exclusions, three-field T, V370 and final coherent replay remain.
