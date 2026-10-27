# Op5 installation: checked batch carrier countermodel

Branch codex/cx-op5-install-20261025. **Op5/P6/Q1 closure is NOT established.**
The deliverable is a checked counterexample to interpreting the retained
arbitrary child carrier on the SAME accepted execution. It is not a
shipped-source/frozen2 disagreement or a false-hash execution of native Rust.

## Exact checked claim

`lean/Op5I_AcceptedBatchCarrierCounterexample.lean`,
`AspisR1.Op5I_AcceptedBatchCarrierCounterexample.accepted_pair_batch_carrier_counterexample`.

Given EXACTLY the accepted_pair_claims native/SDK/std/runtime/extraction/
acceptance/child/marks hypotheses (E specialized to Bytes × State), the theorem
calls accepted_pair_claims ONCE and retains its SAME f,s,outer and SAME selected
semantic/Claims. It constructs a second ChildConeJoin and both of its marks
proofs. The SAME native functions, source Ops, accepted wrapper equations,
external inputs and ordered outer call returns remain unchanged. The second
expanded execution uses the SAME outer log and SAME f,s; no second accepted
native execution, independent source cut, caller output or successful op5
return is assumed.

In this second admissible carrier, BOTH batch0 and batch1 are immediately
followed by a fabricated child read `(a,d)` with `d ≠ H a`. These events are
inside the batch-to-query segments. Its child read list differs from the
trace of EVERY `Program Bytes State R` evaluated under H, hence also every
frozen2 batch program. This is stronger than merely differing roots or
acceptance decisions. All construction and contradiction proofs are checked.

This is a RELATIVE countermodel: from any instance of the accepted native
premises, it constructs another permitted observation of that SAME instance.
No independently fully instantiated SDK accepted fixture is claimed. The
original ChildConeJoin and marks are retained inputs; the new port and marks
are derived outputs, not additional admissions.

## Before / after and precise scope

Before: accepted_pair_claims permits arbitrary
`port : ChildConeJoin E (sdkOps adapterOps ops B claimsStd)` with FirstMarks
and SecondMarks. ChildConeJoin.erasure relates returned values only.

After: unchanged native premises imply the existence of a port satisfying
those same erasure/marks types and, on the SAME outer native execution,

```
full (children badPort) outer = pre0 ++ [.site .batch0, .child (a,d)] ++ post0
full (children badPort) outer = pre1 ++ [.site .batch1, .child (a,d)] ++ post1
d ≠ H a
∀ R code, readEvents (full (children badPort) outer) ≠ (eval H code).1
```

Quantifiers over the source dictionaries and native functions remain
unrestricted; E is specialized to the admissible read-record carrier solely
to exhibit the countermodel. No security metric, failure event, source
function or Result carrier is changed. No hypothesis asserts an effect law,
indexed authentication, whole-body equality or successful caller cut.
The countermodel works for EVERY source dictionary, so fixing op5 alone
cannot make the arbitrary retained carrier into an actual oracle trace.

Discharged assumptions: none of the op5 release/source premises. Added trust
or crypto hypotheses: none. Retained: every original accepted_pair_claims
SDK/std/runtime/source/extraction/oracle/acceptance/marks hypothesis. The
later Required14 conditional child/history premises are neither instantiated
nor weakened; the original Claims/cuts are retained unchanged.

The counterexample invalidates the proposed inference from the existing
arbitrary carrier contracts to native hash-effect transport. It DOES NOT
prove that a concrete correctly source-associated event interpreter cannot
be built. It DOES NOT falsify multiproof authentication outside the existing
collision event or prove a Rust/frozen2 mismatch. No collision-free or
indexed-recovery premise has been smuggled into the accepted theorem.

## Next concrete obligation

Supply a source-associated reification of the actual batch digest calls and
an explicit association of that reification with the selected child carrier,
or explicitly change the target to a separately constructed canonical
carrier. The present erasure/marks records cannot provide this association:
the checked batch-local countermodel satisfies all of them. This is an
implementation/effect association obligation, not a new cryptographic trust
item. No model/source/contract change was made by this worker.

Concrete op5 source installation, P6Boundary discharge/reduction, native
batch Result/scratch/effect refinement and Q1 indexed selected-map recovery
against committed roots remain OPEN. No row closure or100-bit conclusion
is claimed. The existing Port4B accepted-only rejection ruling is respected;
the known panic/Parse lowering issue is not used as this counterexample.

## Validation, resources and freeze

Budget **9/60 Lean attempts,0/20 Kani**. No dependencies were rebuilt.
All runs reused the approved coherent SInt2 workspace and its existing
S2W_lean_host.py/S2W_run_host.py. Each ran ONE module with
`lake env lean -j1 -M7000 -DElab.async=false` in its own systemd scope,
MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64.
No cap increase, timeout, memory kill, unchanged retry, launcher/cache repair,
large generation, package replay or frozen manifest run occurred.

Final focused checks (swap0 throughout):

| Attempt | Exact target | Exit | Wall seconds | Peak RSS KiB | Source revision |
|---|---|---:|---:|---:|---|
|002|Op5I_EventCounterexample.lean|0|2.11907296202844|5141728|4dfb9dccec5ce1289c8cabe88b125e6378fd5aea|
|005|Op5I_AcceptedCarrierCounterexample.lean|0|2.1906308690086007|5147876|ca5b6ce6be9eb8d8b7abdec25f97e6f330d9e0d3|
|008|Op5I_BatchEventCounterexample.lean|0|2.44463070796337|5153280|1244dc2c5c76dd5fc2433bb538df2ce421c04f59|
|009|Op5I_AcceptedBatchCarrierCounterexample.lean|0|2.8482364990049973|5143980|1244dc2c5c76dd5fc2433bb538df2ce421c04f59|

The receipts contain full revisions (table abbreviations are for readability),
exact source SHA256/snapshots, dirty-new-source flag, selected direct object/
sidecar hashes, tool hash, command, exit,wall,RSS,swap,cgroup limits and full
axioms output. Every one of the18 final top theorem audits uses only a subset
of propext, Classical.choice, Quot.sound. Failed001/003/006/007 and their
source snapshots are retained and excluded.006 required explicit list types;
007 required the empty-list append reduction. Each replacement changed source.
004 is a successful predecessor strengthened by005, not an unchanged rerun.

source-pins.json records the unchanged D188 extraction boundary, emitted batch
module, shipped source bodies, accepted_pair_claims and inherited coherent
closure manifest. No new Charon/Aeneas extraction was run or claimed; this
countermodel is independent of source slot implementation. These are focused
checks on the pinned cached selection, not a fresh coherent release replay.

No shipped file or cfg(kani) module changed, so no three-ELF rebuild trigger.
Inherited SHA256s, NOT newly reproduced or reconfirmed:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Only new Op5I_ modules and evidence/op5-install-20261025 changed. No existing
proved module, session A worktree/candidate, key, feature, parameter or wire
format changed. No Rust/Kani/SBF job, new tool, object/binary/archive commit,
merge or push. Stage commits are local. All jobs launched here are terminal.
