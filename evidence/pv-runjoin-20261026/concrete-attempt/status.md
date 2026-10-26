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

## Stage2: exact log support

Read sibling heads again: rw821157fbdd, cbae7b807bef,
dict1f5f2545ea, CTv2b2f95e269a (committed sources read-only).
23406's refused admission was followed by a wait until23407 at14:37:21UTC.
23407 rejects syntax using Lean's reserved `prefix` token plus unreduced local
lets. 23408 fixes those and accepts the two model-log declarations, but rejects
one conjunction projection in encode_nonempty. 23409 changes that projection
and passes2.59s,4231156KiB RSS,swap0,all three axiom reports standard.
Compiler-generated sorryAx reports in rejected modules are never accepted.

PV_RunJoin_EncodingSupport proves:
- every emitted model attempt's log includes the init read;
- the actual model firstGood/some branch has a nonempty complete oracle log,
  including the retained verifier prefix and arbitrary adversary suffix;
- the publication encoder preserves log nonemptiness, even on malformed logs.
The encoder proof uses its retained prefix, not evaluation of a large parser
or recurrence. This is a publication/model fact, not native V338 closure.

23410 admission refused14:41:50.960073UTC. No source transfer or scope.
Next admission not before14:44:50.960073UTC with23411.

The dependent ErrorViewObstruction statement compares the exact reencoded
source experiment and its complete observer log. It is conditional on that
source's actual selected-success coin. To claim an endpoint counterexample,
we still need a concrete native observer decoder and one shared model-success
coin OUTSIDE the unchanged bad event. Neither is claimed here. E1's allowance
of failure and the measured source-helper fault alone do not refute privacy.

## Unfinished concrete construction (no change of contract)

The requested concrete runtime/boundary is NOT supplied. The record remains
8→8 and free data parameters2→2; all eight fields are retained verbatim.
The fault/encoding diagnostics do not authorize an E1 availability assumption,
new bad event, different simulator, restricted observer, made-up nativeWeight,
or default-failing callback dictionary. None is introduced.

In particular:
1. BodySourceLaw still needs a native dictionary/world installation, not just
   emitted source equality at a supplied dictionary.
2. Native File/Error and returned-world effects still need association with
   the model ledger; Formatter/fallible-store transport does not provide it.
3. Native disclosed-byte and complete observer decoding remain data to define
   from the actual source execution, including errors and prior attempts.
4. Native completion weight/frame/fault/coordinate associations remain open;
   CT arithmetic equivalence does not provide this probability factorization.

Next concrete deliverable is the actual native error-world observer producer
and its comparison to the exact original source/bad event, then the frozen
body/dictionary/world construction. No claim of premise removal or successful
completion follows from these diagnostic lemmas.

23411 refused14:45:06.220791UTC,23412 refused14:48:31.092124UTC,
after the required waits; no host scope or source upload followed either.
Continued with the explicit small-local-new-module allowance in pv-common
ruling(c) and local-lean rule1. Existing read-only J/backend objects were
copied locally; no dependency build, infrastructure repair, cap increase or
host admission bypass occurred. Local Lean githash and mathlib git revision
match the predecessor/host pins. No copied Linux native library is used by these proofs.

23413 rejects before elaboration because Lean resolves the first R1Z namespace
root as a whole: its empty objects/R1Z shadows the shared-cache directory.
23414 changes that CACHE ENVIRONMENT by adding read-only links to the existing
same-namespace objects (local-namespace-cache.json). It elaborates the source
but rejects omitted proof-only section variables k/selected;31.04s,
3163029504B RSS,swap0. 23415 changes source by explicitly including selected;
passes28.73s,2987147264B RSS,swap0,both reports standard. No rejected object
is accepted. These are small focused cached local checks, not a release replay.

ErrorViewObstruction.empty_native_log_disagrees now states the model-success
hypothesis explicitly. It is NOT a concrete outside-bad witness, native
observer decoder or privacy counterexample. No premise has been removed.
The latest rw head bf63a9602a preserves the measured entropy factory bytes;
native-factory-branch-pins.json records exact source/function/scan hashes.
The older CTv2 entropy factory is different and is not substituted for this
measured source. CT arithmetic/equivalence receipts are not replayed here.

23416 is the single focused final axioms audit: exit0,25.16s,
3181051904B RSS,swap0; all12 printed theorem reports use only
propext/Classical.choice/Quot.sound. Full signatures retain the entered-draw,
primitive-reply, selected-model-success and empty-native-log hypotheses.
No whole frozen manifest or native release replay is claimed.

Scope correction for progress wording: client_os_error is a theorem of the
shared-world interpreter and emitted Draw64 prototype owner. It is NOT a
complete refinement of the actual RealR1_client.prove_for_proof_accounts
entry. The native probe measures the selected entropy factory only. These
facts do not compose into native V045 without the still-missing association.

All five new Lean sources and cache objects are archived under the assigned
host directory in sources/fault-audit-5c5b9846ff/R1Z and
objects-fault-audit-5c5b9846ff/R1Z. The archive uses zero requested reservation
because it starts NO scope; it does not waive reservation for any build.
All10 archive hashes match local sources/objects (host-archive-sha256.txt).
Objects remain cache-only, are not committed, and do not certify a coherent
frozen deployment closure. No wallet/account/key operations occurred.

Fresh allocation used11/100 Lean attempts (5 accepted invocations,6 rejected
inputs/proof attempts),0/15 Kani;89 Lean and15 Kani remain unused. The required
concrete instance/full-budget deliverable is NOT completed. No full-target
counterexample or legitimate budget exhaustion is claimed as a stopping
condition. Before/after and all eight exact retained statements are in
endpoint-before-after.json; budget-and-result.json records the shortfall.
