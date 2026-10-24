# Concrete factory continuation, unmerged and unadopted

Branch codex/cx-prover-rw-20261023; base3e136e21b9. Design committed before
execution asf164604367. No shipped source, protocol, feature, wire, security
contract, installed tool, wallet/key/RPC/chain, trust, merge or push change.
Both deployed targets remain **not yet established**.

## Exact established relation

Kani051 verifies the unchanged generate_for_mask_nonce returns RepeatedZeroBlock
for public nonce zero without calling fill. Kani054 verifies arbitrary nonce:
zero still makes no call; nonzero makes exactly one fresh-zero64 fill, with
arbitrary64 postbuffer contents and arbitrary custom-u16 getrandom Error, then
returns Os with the identical error. A ghost provider u64 token may advance on
Err and remains at the last chosen value. Arbitrary postcontents overapproximate
all partial-write final buffers; the internal write history is not modeled.
Actual source Result/From, buffers, moves and Drop glue are retained. Only the
existing OS fill primitive is stubbed; no successful or nonzero draw is forced,
no destructor or cleanup axiom/logger, and no output-equality premise is used.

054 is an explicit first-draw-Err path lemma. It does not prove successful
returned32 owners, sixteen rejected draws/final error, or all-error-code coverage.
Error::new_custom spans arbitrary u16 custom codes; real OS/internal error code
identity generalizes only by inspection of the unchanged unconditional From,
not a universal Kani proof over that representation. The ghost token is not a
source refinement of real OS hidden state. No uniformity, freshness,
independence, E1 law or adaptive outer-caller transport follows.

## Retained failures and cleanup boundary

052's all-outcome harness timed out240s during symbolic execution. inspect001
identified the real retry loop;053 reduced ONLY that loop's proof unwind from66
to17, kept every unwinding/pointer/safety check, and also timed out240s. Neither
produced a failed assertion, counterexample, or accepted proof. No time/memory
cap was raised. All-outcome/retry/returned-seed relation remains open.

Fresh Charon049 successfully extracts the exact factory items with precise
drops and actual zeroize bodies. Source-map pins original whole-file,
prefix-through-body and each included span; source.py --check passes.
ProverRwFactoryCleanupAssociation.md maps actual caller locals/drop sites and
returned type field glue to the previously checked Zeroizing32/64 components.
The fresh graph still contains generic projected/trait Drop and an opaque
Iterator::next returning Option<&mut T>. No concrete-only monomorphization or
new Aeneas/backend attempt was made;014 remains fail-closed,015 unaccepted.

Reused native-owned-drop045/046/049/050 match all five pinned zeroize1.8.1 source
files;047/048 are superseded for lifetime reasoning. These are sequential
payload/frame Kani evidence plus a source safety argument. Actual caller glue
executes in054, but this does not observe its physical payload afterward or
mechanize exactly-once/order/erasure transport at P6. That producer remains
open, together with unwind/abort, unknown captures/loans, stale copies/registers,
outer8, mutable adaptive proof_account, durable ledger/events, E1/L1/L2/L3 and
native/adoption/performance targets. No theorem premise changed or discharged.

## Evidence and budgets

ledger.json retains full commands/flags, source/dependency/compiler hashes,
revision labels, exit/wall/RSS/swap and N/A axioms; no Lean theorem was emitted.
051: exit0,2.140s,272060KiB;054: exit0,18.001s,505956KiB GNU peak RSS;
Charon049: exit0,0.981s,198192KiB. Swap0. All heavy launches pass full hierarchy
admission before/go under6G/8G/noSwap/Tasks64; maximum populated reservation
40.375GiB. No Lean compile, full manifest, Rust check/test or ELF rebuild ran.

Timeout GNU RSS undercounts killed grandchildren.052's exact process-tree peak
is unavailable (observed CBMC1991040KiB at221s);053 records sampled aggregate
RSS2122996KiB and exact cgroup memory peak2147975168 bytes, not an exact RSS
peak.054 also records aggregate sampling/kernel peak. Do not reinterpret these
metrics. charon-driver hashing is explicitly POSTRUN, not a repaired identity
gate. Cargo normalized only lock comments/order/format in051/054; retained
before/after bytes parse to identical version/source/checksum/dependency graphs.
The supplemental audit denied that byte drift first; failure retained, audit002
checks semantic identity. Job-local inspect.py was renamed to avoid stdlib
shadowing. No verification replay was used to repair these evidence limits.

Cumulative: backend15/16 (1 left); extraction49/52 (3); Lean236/260 (24);
Kani54/60 (6), this step4/4 spent; optimized Rust check/test0/2, one Charon
release command charged as extraction. Stop the monolithic item. Next producer:
a concrete per-iteration factory/control proof with a justified loop invariant,
then real glue invocation/event transport using supported semantics or reviewed
instrumentation-erasure contracts. No generic wrapper substitutes for it.
