# ProverRwFactoryCleanup: concrete normal factory relation

Design committed before execution. Parent 3e136e21b9ce2576ba4d3385e9e0ab8143bad9b8;
branch codex/cx-prover-rw-20261023. Only new proof/harness/evidence files.
No production, installed tool, trust, protocol, wallet, chain or adoption changes.

## Source association and target

Use exact selected source items from unchanged state_only_entropy.rs: retry
constant16, error enum and From, actual StateOnlyAttemptSecrets fields,
entropy_nonzero32, and generate_for_mask_nonce. A generator records full-file,
prefix-through-body and individual span hashes, checks every byte, and includes
these immutable items in a test-local module. Only imports, an enclosing impl,
and harness functions are added. No method, type, Result/error or Drop rewrite.
The unused methods/imports are omitted, not replaced. zeroize=1.8.1 and
getrandom=0.3.4 are exact dependencies. Original private fields stay private;
harness code lives in the same test module.

Only getrandom::fill may be Kani-stubbed. At each call assert fresh zero64 and
prior calls were successful rejected halves; choose arbitrary postbuffer bytes,
arbitrary success/Err, and arbitrary advanced provider state, including on Err.
Use actual getrandom Error values; any representational restriction is reported.
The monitor records ordered call count and last outcome/bytes without changing
source control. It makes no assumption of successful/nonzero entropy or output
equality. Arbitrary nondeterministic choices cover every finite sequence of
postbuffers/results and provider states; this is a sequential transition
simulation, not an OS distribution, independence, freshness or E1 law, nor a
transport for the outer mutable adaptive callback or durable ledger.

Desired assertions: zero nonce makes no call and returns RepeatedZeroBlock;
otherwise 1..16 calls; each entered draw starts zero; all earlier draws were
Ok with at least one zero half; first Err exits with the identical wrapped error;
first two-nonzero Ok returns identical halves and unchanged nonce; otherwise
sixteen successful rejected draws yield RepeatedZeroBlock. Source byte bounds,
normal Result flow, moves and actual zeroize Drop remain enabled under Kani.
Returned Self is normally dropped after assertions; no destructor stub/logger,
forget/leak or retained dead pointer. This verifies normal control/seed behavior
and executes actual caller drop glue; physical cleanup event ordering still
needs a checked source/MIR relation to P6, not just the prior component checks.

## Cleanup and retained obligations

Reuse six native-owned-drop checks explicitly by exact hashes and source
assessment;049/050 supersede047/048 for lifetime reasoning. They establish
sequential payload/frame evidence with a source safety argument, not provenance,
whole-caller cleanup trace or hardware erasure. Inspect actual caller/glue sites
and bind only as far as evidence permits. If instrumentation is needed, propose
an erasure/admissibility argument rather than changing Drop into a logger.
Unwind/abort, stale moved storage, unknown captures, unsupported loans, outer8,
mutable-adaptive proof_account, durable reservation/events, E1, L1/L2/L3 remain
required and open. Both deployed targets not yet established. Existing theorem
premises before/after identical; no hidden output-equivalence premise.

## Validation admission and budget

Start backend15/16, extraction48/52 (new4 allocated), Lean236/260, Kani50/60.
This step maximum4 Kani and2 optimized Rust test/check commands. Charge all
reserved failures and preflights; no unchanged resource-failure retry. Prefer
one all-outcome harness, a small zero-nonce harness, then focused strengthening
only for a specific gap. No backend slot absent narrow supported interface.
No full manifest. All heavy jobs host-only independently6G/8G/noSwap/Tasks64;
full hierarchical system/Docker/child inventory, capped ancestor deduplication,
uncapped visibility, strict<55GiB before/go and exact barrier hashes. Existing
stricter Lean5G/7G and shared global lock outside22:30-14:00 London remain.
Expected time in optimized compilation then named symbolic factory verification,
not arithmetic elimination. Preserve failures; review ten minutes without target.
Record command/flags, exact revision/source/dependency/binary hashes, exit,
wall/RSS/swap and full axioms or N/A. Derived JSON>5MB hash+size only.
