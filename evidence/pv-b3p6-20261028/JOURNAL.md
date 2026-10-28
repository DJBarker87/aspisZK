# P6 continuation of batch 3

Exact worktree: `/Users/dominic/ZK/.worktrees/pv-b3p6`.
Branch: `codex/pv-b3p6-20261028`; candidate: `5fa2cc6781`.
Host: `/home/dombarker/project-offloads/codex-pv-b3p6-20261028/`.
Lean IDs 42500–42599 only; 42597–42599 reserved for final audits.
Budget: 100 charged Lean attempts, 12 Kani runs. One capped scope at a time.
No change under crates/ or programs/. No shared source/object writes.

Read pv-common.txt and restored flag, including all rulings through (p').
External h4 preflight verified all 5673 objects, zero mismatches, before any
compile. Source authority for project closure is EJR/freeze then own tracked
HEAD, with h5' precedence; resolved six-module op133 closure has no missing
module. Recount6 target files are absent from candidate; six exact rows and
ROWS6 lines were read with git show from committed research. authority.json
records that revision. No changes to ledger, trust items, simulator or observer.

## V229 / op133

The shipped original in aspis-statement has no arguments: it builds the
schedule, collects producer/consumer endpoints, sorts and deduplicates. The
owned reference is a literal 214-element array, outside shipped crates. Its
inventory derives from the frozen host copy's 136 MASK_LINKS; that derivation
is only preflight, not the native association. The no-stub Kani harness calls
the original aspis-statement function, checks success, exact length and every
row against this reference, with unwind1026 and unwinding assertions.

charon133-01 failed before extraction because the source snapshot omitted the
three pinned writer crates. charon133-02 then exposed a missing included
pinned glue_gen.rs. Both failures are retained; dependencies were added before
retrying. charon133-03 accepts the actual root (12.072s, 543968KiB, swap0).
aeneas133-01 accepts under unchanged pinned extractor/strict joins
(0.227s, 55264KiB, swap0). The B1 port changes only imports. There are no
mutable-borrow writes or backward continuations in the literal reference.

kani133-01 fails compilation on omitted proof-only tree.rs in the snapshot.
After uploading its pinned tool sources, kani133-02 exposes 21 pre-existing
proof-only records caller arity errors. The proof-only compatibility wrapper
in tools/r1-builder-reference/records.rs calls the unchanged seven-argument
shipped records with pair_empty_roots(), preserving the old helper convention.
It neither stubs nor changes the op133 closure. kani133-03 runs with this
source repair; timeout900s, taskset0–3, MemoryHigh6G/MemoryMax8G/swap0/Tasks64.
The 900-second gate is the first solver run, not a retry after a180s timeout.

Lean law and original-carrier installation are drafts until compiled.
Native differential is queued and will be labelled finite validation.
No row closure or endpoint premise removal is claimed at this stage.

## Other target rows

V228/op132, V241/op224, V243/op226, V244/op227 and V245/op228 remain OPEN.
The inherited batch3 extraction refusals/failures are not counterexamples.
Field arithmetic in op224/op227 requires structural or Lean correspondence,
never chained-field Kani. Finish op133 before starting partial work on them.

T remains exactly entropy_law, entropy_kernel, observation.
Target not yet established.

Ten-minute gate review: no new proof target has completed during kani133-03.
The obligation is a singleton-input control-flow/indexing/sort calculation,
not chained field arithmetic. Memory caps are unchanged and will not be
raised. Retain the current 900s timeout; on timeout inspect the exact phase
and shrink/split the bounded harness before another run. The frozen original
collects at most272 endpoints; a273 unwind split can test whether the1026
bound created pathological symbolic sort expansion, with unwinding assertions
still enabled. A failed candidate is retained and is not a row counterexample.


## Checked op133 proof packet and gate refinement

42500 accepts the raw reference.42501 retains a syntax/default-simp recursion
failure in the independent literal table;42502 accepts the explicit rfl length
certificate and Array.length_eq, without changing Lean limits.42503–42505
compile the original ExternalTypes/Types/ExternalFuns privately from h5 tracked
sources.42506 retains an opaque-Usize bound and do-syntax draft failure;
42507 accepts scalar bounds, the complete-Result reference equation, successful
non-vacuity and261 other-field frames (264 axiom reports, all standard).
No inherited source or shared object changed. Native133-01 passes the one
same-input original/reference inventory test, explicitly finite validation:
exit0,18.716s,567520KiB RSS,swap0. The native/ref bodies remain unchanged.

Kani133-03 times out at901.119s after4.40s optimized compilation. Its
/usr/bin/time peak15644KiB measures the terminated timeout-parent collection,
not the full child set; cgroup.memory.peak is6840975360bytes and swap0.
Do not interpret that small RSS number as CBMC's memory use.
Kani133-04 changes the global bound to273; resource review stops only this
job's verified CBMC PID at347.062s, exit1,6607208KiB RSS,swap0,
cgroup peak6784745472bytes. It had not reached the SAT solver. This is a
retained failed candidate, not a source counterexample or a job stop.

Loops133-01 is a capped read-only goto loop inventory, no symbolic proof
run (exit0,.485s,55316KiB RSS,swap0). The46 candidate per-loop bounds are
recorded in bounds133.json, with unwinding assertions retained. Iterator
inner traversals get3, source traversals get their literal lengths, and
sorting/dedup/recursion get separate bounds. A new explicit214-word equality
loop avoids the old428-byte memcmp. Kani133-05 is the changed candidate;
no stubs or input restrictions are introduced, and it has no correctness
credit until all assertions pass. Eight charged Lean attempts and five Kani
runs submitted; the loop inventory is not counted as a Kani proof run.

Kani133-05 also grows to6GiB before SAT; the own CBMC is stopped after
395.116s (exit1,6584124KiB RSS,swap0). The next candidate enables the bundled
CBMC's documented path-at-a-time lifo strategy and dereference caching,
with identical source, assertions, bounds and caps. Kani133-06 is refused by
the outer reservation (exit78,allowedfalse; zero Kani runs). After the full
180s cooldown,06-r1 passes outer admission but the inside barrier refuses
because another scope races into the reservation; no compiler starts. Wait
another180s and retry a fresh label. Counts remain8 charged Lean/5 Kani.

## Serializer continuation and updated lead rulings

Owned serializer extraction charon226-02/aeneas226-02 accepts the actual
public_bytes root. The borrowed projection candidate's abstraction failure is
retained. The accepted candidate moves an owned Source, serializes23 explicit
64-byte chunks, and preserves all16 mutable array restoration continuations.
Native226-01 passes four same-input cases (both variants and rejected inputs),
finite validation only. Emission/native validation is still pending.

42509 Output133,42510 Result133,42512 Extensionality133 pass;42508/11 are
zero-charge refusals.42514 BytesTypes226 rejects an unsupported discriminant
attribute; removed metadata only, without changing constructors.42513/15/16/17
are zero-charge admission refusals. Next unused ID42518;12 charged compiles.
Seven actual Kani runs, no PASS:06-r2 and07 time out at900s. Auxiliary u8
index in07 is supported by the checked extensionality theorem; no input
restriction was used. No checked counterexample to a target row exists.

Read new rulings(r),(k'),(r') and pin the exact KMX patch/usage from research.
Copy-dependent PASS results require that patch and a failing negative control.
No native link is inferred from the failed or timed-out gates here. Evidence
class for any future structural fallback will be structural (K-1 substitute).
All six rows remain OPEN. T retains its original three fields.

42519 accepts serializer Types.42520 times out monolithic emission after
900.612s, exit124, peak RSS9198824KiB, cgroup peak7070253056bytes, swap0,
no axioms result. The ten-minute review held the cap and timeout fixed.
No unchanged rerun. The exact nine emitted definitions are partitioned into
seven modules, with per-definition body hashes in split226.json. Smaller
scalar/indexing/projection declarations are tested before the64-read chunk.
The split8 Rust candidate remains an unused alternative, not a source change.

Declaration isolation:42521 retains a dangling source-doc-comment syntax
failure in the partition, not a theorem failure; documentation removed while
all definitions and original ZERO metadata are preserved.42522/23 are
zero-charge refusals.42524 ByteField226 and42525 ByteAt226 pass.42526/27 are
zero-charge Result-algebra admission refusals; queue observes full180s waits.
17 charged Lean attempts so far;7 actual Kani runs (the old host tally's6
is stale, not an eighth unrecorded run). No row removed.

The supplied KMX_CopyMeaning source is retained as .lean.txt, an uncompiled
source artifact, to keep every compiled/new Lean module under PV_B3P_. The
exact patch and byte-exact Rust replacements remain pinned. No KMX theorem or
compiled Stream A object is imported. The selected negative growth control
and patched op133 recheck are prepared but not yet run. No Kani PASS claimed.

## Exact-patch native recheck priority

42528 is a third zero-charge Result-algebra admission refusal. The idle
focused queue (verified sleeping with no child) was stopped to prioritize
finishing op133 under newly available mitigation. No scope was interrupted.

KMX growth negative control01-r2 is admitted after two refusals:exit1,
19.438s,307408KiB RSS,swap0,cgroup peak513216512bytes,revision5a7d64d577.
Its sole failed check is the intended false assertion dst[16]==0 at exact
KMX_stubs.rs:75 (1/395 checks failed); this is not a target-row counterexample.
Patch SHA bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67;
Rust replacement SHA ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
The original op133 whole-function pointwise harness is now running as
kani133-kmx-08 with all six exact copy replacements, native per-loop bounds,
default1026 for replacement loops and the original assertions/auxiliary domain.
No business-function replacement. No PASS yet;8 actual Kani runs completed,
a ninth in progress.17 charged Lean attempts. All six rows remain OPEN.

kani133-kmx-08 times out900.998s,exit124,swap0,cgroup peak6763036672bytes.
The15660KiB timeout-parent RSS is not descendant aggregate. No PASS/no credit.
CBMC remained the active heavy process near the end, without an observed
Kissat child. Nine Kani runs completed. No unchanged rerun or larger cap.
A changed CBMC representation (no array field sensitivity) will first run the
exact negative growth control under that representation, then the original
op133 property only if the intended assertion is again the sole failure.
This tests the identified array expansion bottleneck; source, assertions,
auxiliary domain and native bounds stay fixed. Two runs would leave one of
12 Kani slots. Lean work continues regardless of Kani exhaustion.
