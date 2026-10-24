# Factory iteration continuation — unmerged, unadopted

Branch codex/cx-prover-rw-20261023, base745f551f8485241f7b5e74bf5945169dbf14b1fb.
Design1280b8fe81 precedes harness55cbf35245 and execution. No crates/programs,
protocol, wire, feature, security contract, installed tool/service, shared source,
wallet/key/RPC/chain, trust, merge, push or adoption changes. No full manifest.
Both deployed targets remain **not yet established**. Current ELF target pins
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
are unchanged targets, not new identity gates.

## Established component

Kani056 passes the concrete one-draw CANDIDATE cut relation, not the actual
factory loop. Full statement and limits: tools/prover-rw-20261023/factory-iteration/
RELATION.md and proof-cut/lib.rs. Every entry count0..15, nonce32, postbuffer64,
primitive Ok/Err choice, custom-u16 error code and ghost u64 provider token is
quantified. The stub requires exactly one freshzero64 call, permits arbitrary
postcontents on Err, and may advance the token on Err. The unchanged actual
From wraps the identical error. Some returns iff both halves are nonzero,
with exact moved32 owners and unchanged nonce; None iff either half is zero,
with retry=r+1 and remaining16-r decreasing by1. Entry15 rejection reaches16.
Success keeps retry unchanged. The arbitrary output index covers all32 bytes.
No desired-result premise, success/nonzero assumption, destructor replacement,
freshness, independence, uniformity or real OS hidden-state refinement.

The cut retains actual zeroize1.8.1 Drop and lexical owner scopes. This is a
sequential source/Kani component check, not native cleanup-event count/order,
physical post-destruction storage, unwind/abort, provenance/loan, stale-copy or
hardware-erasure evidence. The real whole-caller event producer remains open.

## Actual-source relation and retained failures

source.py --check validates original full source/span pins and exact erasure of
055's proof-only annotation.057 has a second explicit frame annotation, both
erase byte-for-byte to the same selected source. No executable source span in
those snapshots is rewritten.055 tests the actual loop invariant and complete
normal Result relation, with actual Drop and every safety/unwind check enabled.
It times out at240s. inspect001 records dynamic-contract write-set inclusion
and original-named loops; this does not identify an exact solver bottleneck.

The fallback candidate is a distinct statement:
actual `generate_for_mask_nonce : nonce32 -> Result<Secrets, Error>`;
cut `one_draw : (nonce32, r) -> Result<(r', Option<Secrets>), Error>`.
cut-source.py --check records exact body factoring, with only success-result
wrapping inside the copied body. Removed nonce guard/loop, entry retry and None
rejection plumbing are explicit. A cut rejection is not factory exhaustion.
Syntactic factoring is not a mechanized source/MIR equivalence proof. The
finite16 ranking argument is documented, conditional on this missing actual
body/caller association; it is NOT an accepted factory composition theorem.
No generic loop theorem replaces it. Existing theorem statements/premises are
unchanged; none was discharged, added or hidden.055 is no proof/counterexample.

## Reused evidence and required next producer

The previous factory-cleanup051 zero-nonce and054 first-fillErr checks are
reused in their original scopes.054 is still custom-u16 only. Charon049's actual
caller/drop graph and source association are reused, not re-extracted. The
native-owned-drop045/046/049/050 five zeroize Rust-file hashes all match056's
before/go inventory; reused-source-assessment.json records the receipts.
047/048 remain superseded for retained-storage lifetime reasoning. These
comparisons are not fresh source-to-binary gates or factory-event proofs.

No accepted actual factory all-outcome, destructor-event, OS-state or E1 producer
was established. Smallest next deliverable: mechanize the concrete cut factoring
against the actual caller/MIR, then its finite16 source controller, preserving
all results, returned moves and normal cleanup. A separate required native
producer must bind real Drop invocation/provenance/order to the checked leaf
with justified instrumentation erasure/admissibility or supported glue evaluation.
The generic iterator/trait Drop graph remains unsupported/unaccepted; no final
backend slot or larger unchanged BMC was spent on speculation.

Outer8, mutable adaptive proof_account, durable ledger, complete observables/
errors/retries, E1 law, L1/L2/L3, nativeclient/refinement/artifact and adoption
remain open. Historical fixedcoin1000/performance is not new validation. All3
ELFs, fixedcoin>=1000, native events/refinement, L1/L2/E1, quiet<15s andH5<=10%
remain adoption gates; no shipped source change or adoption is authorized here.

## New validation, exact resources and budget

057 tests the same actual source with a verified explicit write-set annotation
and a symbolic returned-byte index. It also times out240s, without a proof or
counterexample. No unchanged resource retry, cap/timeout/unwind increase or
check disabling occurred. Stop this invariant method; no further backend or
proof command is justified by these retained failures alone.

ledger.json and packet/*/preflight.json/receipt.json retain exact commands,
source revision labels, complete source/dependency/toolchain/binary before/go
hashes, fingerprints, exits, wall, GNU RSS, swap and N/A full axioms results.
All560-or-more pinned inputs are checked again inside each verification scope.
Each postrun audit records no changed input bytes at that run's completion.
Later new job files are not retroactive inputs. Revision labels plus per-file
hashes identify exact inputs; labels do not assert every later audit script
was already committed at that revision. Inspector script identity is its
preflight hash, with the cut revision as context. No postrun hash repairs an
absent preflight gate. All actual Kani/compiler/CBMC/solver/toolchain and library
binaries are pinned before/go; current deployed ELFs are not freshly checked.

| Target | Exit | Wall seconds | GNU peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| Kani055 actual invariant |124|241.470718|15824 (incomplete)|0|
| Kani056 candidate one_draw_relation |0|31.689034|1802592|0|
| inspect001 existing GOTO loops |0|0.345117|19096|0|
| Kani057 actual explicit frame |124|241.461047|15824 (incomplete)|0|

056 reports0/462 failed,4 unreachable. Its sampled aggregate peak2259732KiB,
cgroup memory peak2432335872 bytes.055/057 GNU time misses killed descendants:
exact process-tree RSS peaks are unavailable. Their sampled aggregate peaks
are6567208/6571376KiB; exact cgroup memory peaks6704115712/6708342784 bytes.
These memory peaks are not RSS peaks. Peak swap0 throughout. Every scope uses
6G/8G/noSwap/Tasks64 with full-hierarchy before/go admission; maximum projected
reservation32.375GiB, strictly below55. Kani compilation is optimized; no heavy
arithmetic/extraction is run in debug. No Lean declaration, compile, imports/
axioms replay, Rust check/test, extraction, backend build or ELF rebuild ran.
`#print axioms`: N/A throughout, not omitted Lean output.

Cumulative budgets: backend15/16 (1 left), extraction49/52 (3), Lean236/260 (24),
Kani57/60 (3). This step3/4 Kani spent (1 permitted left), optimized Rust
check/test0/2; extraction/Lean/backend increments0. All failures charged.
Derived JSON/binaries from Kani remain host-side; postrun.json retains hash
and size only. No derived JSON over5MB or compiled object/binary is committed.

Local final-audit.py (no build/replay) passes exit0,0.306568s,101892096-byte
macOS peak RSS; swap count N/A (not exposed by macOS time). Exact command,
revisionfab2fb121f and script/input hashes are in local-audit-receipt.json.
It checks annotation erasure, cut factoring, every host receipt fingerprint/
cap/admission, no shipped-source diff, and absence of compiled or oversized
JSON artifacts. It does not turn cut factoring into semantic equivalence.
