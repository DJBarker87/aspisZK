from pathlib import Path
import json,collections,hashlib,subprocess
E=Path(__file__).resolve().parent
read=lambda n:json.loads((E/n).read_text())
def main():
 c=read('KNE_COVERAGE.json');runs=read('KNE_RUNS.json');remaining=read('KNE_REMAINING_RUNTIME.json')
 counts=collections.Counter(r['kind'] for r in runs)
 complete=c['covered']==116
 decision=('RESTORED on the reachable domain, conditional on the exactly named driver hypothesis and retained oracle/allocator/library/source association obligations.' if complete else 'SUSPENDED: missing concrete transition credit remains. The composed Lean leaf theorem is proved conditionally and does not supply missing runtime credit.')
 manifest=[r for r in runs if r['sources']==['KNE_Final.lean'] and r['exit_status']==0]
 assert len(manifest)==1,'one successful final manifest required'
 final=manifest[0]
 text=f'''# KNE checkpoint leaf finding

**{c['covered']}/116 transitions credited; {c['remaining']} remain. Checkpoint leaf credit: {decision}**

## Derived schedule

`AspisR1.KNE_Model.bodyEmissions_payload` proves that the source-ordered individual payloads flatten to the adopted cohort field model, including the same 64 weights. `bodyEmissions_shape` derives widths from serializer length lemmas. `KNE_Schedule.derived_schedule` proves the resulting annotated schedule equals `KND_Schedule.schedule` exactly; no difference was found. It has 116 appends, capacity 1768, final length 1768 and no growth. `caller_final_len` derives 64 from the frozen S2 transport arithmetic. The body has 115 writes and 1736 bytes; the checksum is write 116. [Model](KNE_Model.lean), [schedule](KNE_Schedule.lean), [metadata](KNE_SCHEDULE.json), [export provenance](KNE_SCHEDULE_PROVENANCE.json).

`KNE_Writer.cohort_program_eq` identifies the source-shaped sequential append refinement with the adopted cohort writer program for EVERY oracle reply. Materialization consumes the derived body emissions; the checksum append consumes that SAME body. This is a refinement of the adopted byte model, with the retained physical Rust/source/library association boundary; it is not a new allocator extraction theorem. [Program bridge](KNE_Writer.lean).

## Caller domain

Unit 34 of `../native-inv1-20261027/NBI1_INVENTORY.md` establishes the intended driver cut: SAME accepted k10/S2 run, accumulator next 10 after flush, 64 canonical weights, 22 bounded queries, exact proof/public carriers. That inventory explicitly leaves executable driver composition open. This job therefore retains precisely ONE named driver hypothesis:

`AspisR1.KNE_Caller.DriverEstablishedDomain Reached`

It says every SAME reached p,a has `S1S7S8StateProvenance` with its SAME pm,am. `every_reached_call` derives the writer domain. No independent checkpoint, inventory, accepted run or whole-output equality is supplied. The enclosing driver proof is not claimed merged. [Caller](KNE_Caller.lean).

## Transition coverage

Inherited KND credits: 43. Newly completed transitions: {c['new']}. KNE pairs: {c['new_pairs']}/75. Statuses: {c['statuses']}. Each positive fixes its exact(len,1768,size), keeps live initial/appended bytes arbitrary, asserts length/capacity and its observation window, and has an identical XOR1 control. Every credited control fails the selected byte assertion, rather than a safety assertion. All 116 scheduled triples are distinct; no nonidentical transition was deduplicated. [Pairs](KNE_PAIRS.json), [independent audit](KNE_PAIR_AUDIT.json), [coverage](KNE_COVERAGE.json), [exact remainder](KNE_REMAINING_RUNTIME.json).

The four KND timeout attempts concerned weight53 and checksum. Their replacement positives/controls split indices into [0,len) and [len,len+size); both windows must earn matched credit. Neither unchanged timed-out shape nor any timeout receives credit. The harness remains `KND_transition`; no function/module was renamed to obtain a verdict. The task input file is `KNE_windows.rs`. There is no `Option<fn>`, function-pointer comparison or observer in any new harness; quarantine list is empty.

The exact inherited KMX stubs are reused, never reimplemented: SHA256 `c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9`; inherited patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Vec::from(array1768)/truncate initializes spare bytes; these gates do not claim an additional universal uninitialized-spare heap refinement. Physical source/library/allocator interpretation stays at the retained boundary.

## Composed leaf statement and ruling (v)

`AspisR1.KNE_Leaf.native_result` composes the 115 actual body writes and the checksum append over the derived schedule. Its result has length 1768, equals `LPm_CheckpointProgram.returned`, equals `OraclePortCheckpointAbiC5.encode` under the retained oracle interpretation, and carries the chronological proof/public/checksum read log. The checksum observation uses the same 1736-byte physical body. Local runtime laws are explicitly represented by `KNE_Composition.LocalCorrect`; Kani receipts interpret those laws under the retained source/library boundary and are not imported as Lean axioms. [Generic composition](KNE_Composition.lean), [leaf](KNE_Leaf.lean).

Ruling (v), C3-BIN, narrows the leaf's DOMAIN to reached S2/final_len64/weights64 calls. It does not weaken byte equality on that domain. The nine original arbitrary-prefix/cap=len/growth1736-to3472/caps128/256 harness rows are SUPERSEDED for this leaf, retained and uncredited, not deleted or retroactively confirmed. No enclosing driver/runtime/ABI/source-to-ELF or headline theorem is newly closed. Decision: **{decision}**

## Validation and resources

Budget used: Kani {counts['kani']}/150, Lean {counts['lean']}/50, optimized Rust 0/5. No unchanged regression or manifest rerun. Rejected local proof snapshots and receipts are retained; their sorryAx/error-recovery outputs earn no credit. SourceBody stays opaque; local recursion-limit errors were replaced symbolically, without increasing limits. Every accepted new top has only propext, Classical.choice, Quot.sound (or a subset).

Frozen Rust revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen Cargo.lock SHA256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Reused scratch crate KMY_src retains its copied frozen lock. Before EVERY Kani run, the resolved graph is validated against that lock; CARGO_NET_OFFLINE=true, opt-level3; lock hash checked unchanged afterwards. No new Rust native run was needed for frozen unchanged shipped code.

All scopes are serial, MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64, Lean-M7000; admission requires JSON allowed:true AND exit 0. The unchanged KMY admission wrapper enforces both before submission. SSH 255 steps wait 60s/retry up to 10; submitted attempts are recovered read-only, never resubmitted. The local Kani queue pauses drained at pre-submission boundaries before focused Lean checks; each resume followed terminal Lean receipts. [Transport](KMY_TRANSPORT.jsonl), [submission recovery](KNE_SUBMISSION_TRANSPORT.jsonl), [pause receipt](KNE_QUEUE_PAUSES.jsonl), [exact run index](KNE_RUNS.json), [source pins](KNE_SOURCE_PINS.json), [current Lean hashes](KNE_CURRENT_LEAN_SOURCE_AUDIT.json), [resource audit](KNE_RESOURCE_AUDIT.json).

Final manifest: {final['sources'][0]}, exit {final['exit_status']}, wall {final['wall_seconds']}s, peak RSS {final['peak_rss_kib']}KiB, swaps {final['swaps']}, source revision`{final['source_revision']}`. [Receipt]({final['attempt']}/receipt.json), [final import/axioms audit](KNE_Final.lean). The exact final receipt path is `{final['attempt']}/receipt.json`.

All 150 owned compiler/solver temporary directories were removed by the existing gate cleanup; no own scope or scratch object remains. [End inventory](KNE_HOST_END_INVENTORY.json), [cleanup](KNE_CLEANUP.json), [timeout replacements](KNE_TIMEOUT_REPLACEMENTS.json).

Persistent cache `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028` is retained. No crates/programs, wallet/account key or authority changed. Commits are local; no push.
'''
 (E/'KNE_FINDING.md').write_text(text)
 print(c['covered'],decision)
if __name__=='__main__':main()
