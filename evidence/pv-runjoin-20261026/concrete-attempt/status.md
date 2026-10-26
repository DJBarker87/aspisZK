# Concrete-instance continuation

Target not yet established. Entry revision: 92a6c256a6.
Fresh allocation: 100 Lean compiles, 15 Kani invocations; IDs23400–23699.
The requested free-parameter change has NOT occurred: runtime/boundary 2→2.
The endpoint's eight fields and exact conclusion are unchanged.

## Source inspection

Read pv-common, r1p-common, local-lean, root AGENTS security/proof discipline,
effect-client/handoff and PV_RunJoin_Endpoint before proof work.
Sibling aliases resolve to codex/cx-prover-rw-20261023 (rw16),
codex/pv-cb-20261026 (cb), codex/cx-prover-dict-20261026 (dict9).
Their committed sources are read-only. CT v2 is
codex/cx-ct-kernels-v2-20261022. No sibling checkout is changed.

PDict_StoreTransport.reserve transports the exact emitted fallible store
between opaque IO-error/Formatter representations. It explicitly leaves
native File/Error world association separate. It is not a proof that the
native ledger is ProverCommitLedger36.reserve (V337).
PV_CB_Composition.selected explicitly retains unassigned dictionary fields.
ProverRwSuccessBodyInterpretation.selected installs selected points and S2
coefficient source leaves; it retains the D callback and input dictionary.
These facts cannot by themselves define all the frozen native runtime data.
CT-kernel equivalence is not the probability factorization stated by V339.

## Fault audit

New source: PV_RunJoin_FaultAudit.lean. Pending acceptance until receipts say
otherwise. owner_os_error carries an arbitrary partially written64-byte
buffer and exact native error through the emitted Draw64 owner.
client_os_error composes that path through the shared-world client, preserving
the returned account world and advanced provider. The body is arbitrary and
is not executed. E1_allows_total_failure records that conditional E1 allows
zero success availability. These are source-control/model facts, not an
installed native dictionary or a counterexample to the privacy headline.

Before discharging V038, the same fixed bad event must be checked against
this failure path. No success assumption, extra bad event, availability
axiom, altered simulator or fault-erasing decoder is introduced.

## Resource/admission history

23400 compiled and failed before elaboration: missing UnifiedPaths cache.
The successor removes that dependency and proves the client path directly.
Only missing predecessor cache objects are restored; no existing object is
overwritten. cache-23401.json records hashes and source archive location.

23401 read-only admission refused14:25:17.686536UTC; no transfer or scope.
23402 read-only scan14:26:20.960789UTC was premature: an operational mistake.
It launched no scope and does not waive the wait. No next transfer/launch
before14:28:17.686536UTC; use next unused ID23403. Refusals charge zero Lean
attempts. The launcher and resource infrastructure are unchanged.

23403: changed imports and direct client proof accepted the two source-control
lemmas, but the module was rejected because the kernel-zero theorem omitted
its successful carrier annotation. 23404 adds that annotation and passes:
2.26s,4279416KiB RSS,swap0,all three axiom reports standard.
23405: normalized/nonnegative availability-kernel facts pass2.53s,
4278560KiB RSS,swap0,all four axiom reports standard. E1 permits the normalized
zero-success/one-error distribution, not merely an unnormalized zero function.

Native01: optimized build passes1.38s,195576KiB RSS,swap0. Probe fails101:
getrandom0.3.4 intentionally falls back to /dev/urandom when its initial
getrandom availability test gets EPERM. This is retained as a failed TEST
SETUP, not as a counterexample to getrandom or to the prover.
Native02 changes the process-only filter to EIO (no fallback), and pins cfg-if
1.0.4 to match the predecessor probe dependency. The unchanged selected
factory returns Os(EIO) on public nonce[1;32]. This is a source-helper native
fault observation, NOT a whole-client/privacy counterexample. No OS callback,
zeroization implementation, source error mapping or production source is
stubbed/changed. The filter is installed only in the probe process.

23406 admission refused14:34:05.013466UTC; no transfer/scope. Next admission
not before14:37:05.013466UTC with ID23407. Useful proof writing continues.

## Stage1 accounting

No endpoint premise removed, added or weakened. No whole ledger row closed.
Record remains source_V045, E1_V329, native_fill_V336, native_ledger_V337,
byte_blind_V338, kernels_V339, disclosed_V038, observerOracle_V038.
The new results make one required failure path exact; they do not construct
runtime/boundary, install a native decoder or establish V038. A native helper
fault is NOT a checked counterexample to the headline. Budget so far4/100
Lean attempts,0/15 Kani;2 optimized native probe runs. All host run receipts
include source snapshots/pins, exit/wall/RSS/swap and axioms or explicit N/A.
No full manifest or unchanged regression was run. No production/soundness,
sibling, launcher, ELF, key or account changes occurred.
