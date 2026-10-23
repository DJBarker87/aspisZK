# Stage 2: owned cuts, exact checkpoint child order, remaining native schedule

## Exact results

`S2Z_OwnedCuts.first_dependencies` inverts the ACTUAL adopted stage1_owned body.
Whole acceptance yields one public read, decoder result, validator result, common
projection, afterstate encoder result, semantic projection and first_decoded call
on the same decoded statement and same public input, with the same returned CP.
Unlike the earlier cut, this also retains the actual afterstate encoder operation.
The source binds occur in the emitted order; this result is a value dependency
certificate, not a native timing certificate. `second_dependencies` specializes
Cuts.stage2_call to retain full extracted validate_asq8, its statement encoder,
tx2 with None, and the same statement's emitter. Child success is derived from
whole acceptance, not assumed independently. No shipped caller is rewritten.

`S2Z_ChildOracle.checkpoint_resume` instantiates the existing checkpoint child's
successful source-log theorem with the digest dictionary transported from the
OWNED extraction. It proves exact append order proof, public, checksum, with the
same source Calls witness, and their ideal observations under the per-call law.
It retains actual resume success, comparison soundness and checkpoint length1768;
it does not infer those from owned stage2 acceptance or equal roots. The
verifierOps/native-child-to-resume effect port is still required.
`consistent_child` composes the same oracle law with the existing effect
interpreter for any returning child, including an inner verifier Err. Initial
log consistency and that child's SAME effectful run are explicit. Outer
fail/div/native VM abort prefix reification is not provided by this result.

`S2Z_Oracle.total_of_returning` weakens the total-call theorem's runtime premise:
success-conditioned RuntimeSyscall plus a separately named returning-domain
hypothesis suffices. Encoded digest identity is derived by array_roundtrip.
The unrestricted totality quantifier in the current lead field is retained.
This is not derived from validity of only the reached native calls.

## Per-field disposition

| Assigned field | Status | Exact remaining boundary |
| --- | --- | --- |
| oracle | Conditional | S2Z_Oracle.successful_call gives checkpoint Oracle under NativeBinding, RuntimeSyscall, P1Realization. S2Z_Oracle.total_of_returning gives the exact Required14 total field with the additional `returns : ∀ parts, ∃ digest, hashv parts = ok digest`. None of these native/ROM/domain premises is discharged here. |
| callOrder | Open globally | Explicit owned source binds and the checkpoint's three-read child order are proved locally. Need actual site/event reification into c.clock, source-indexed first/second child schedule ports, and a history associating TX1's save with this TX2. No ranks are used as native timestamps. |
| reachedPrefix | Open globally | Need first/second whole-child reached-site prefixes on the same invoked arguments, SDK save/write cut placement, and the same transaction history. Neither independent accepted transactions nor child value equality supplies these. |

## Why the remaining join cannot be inferred from current value theorems

AdapterRw.Ops op10/op11/op43 and the other opaque child operations return pure
Result values. The extracted control flow orders their binds, but neither the
operations nor owned caller results contain native effects, clocks, or the lead
Inputs observation. Two calls to stage1_owned/stage2_owned are independent
functions; the extraction contains no transaction-history relation.

`S2Z_ScheduleLimits.no_clock_from_values` formally demonstrates that replacing
only c.clock by constant0 defeats callOrder whenever TX1 and TX2 are reached;
no function input or accepted equation mentions that clock. Its companion
`no_prefix_from_values` demonstrates that arbitrary Inputs.reached need not be
prefix-closed. These records are NOT asserted to be native observations. They
rule out an invalid inference, not the intended native theorem. As required by
proof discipline, the unrestricted value-only closure route is stopped.

Inspected child interfaces: CheckpointBytes5Trace.successful_log supplies an
actual digest schedule; MultiproofConeP6Frozen2Stage.both_batches is a batch
source-program join; S7JoinQueryRows supplies Progress/PushTrace arithmetic;
S8JoinFrozenScan.parsed_y1 supplies the exact scan value. The latter value
results do not export c.reached/c.clock facts or a same-native-run event port.
Their source and hypotheses are reused unchanged. They are not silently
strengthened into complete checkpoint/multiproof/S7/S8 native schedules.

Next concrete deliverable: an execution-indexed effect interpretation of the
actual owned op10/op11 bodies, with local site entry/exit events and rejection
prefixes, plus native snapshot/write and cross-transaction history binding.
Those ports must instantiate the child source joins on the exact cuts exported
here. This is a missing source-refinement proof, not a cryptographic assumption.

## Validation and frozen target

Lean003 (owned cuts),006 (child oracle),007 (schedule countermodels),008 (weaker
totality) pass. Lean004 failed only on ambiguous Parts/Digest names;006 qualifies
them. Lean005 failed on the reserved `prefix` token;007 renames the local binder.
All failed attempts remain retained and excluded from theorem evidence; recovery
sorryAx printouts are NOT accepted. No timeout, memory kill, cap increase, or
unchanged source rerun occurred. Full metrics, exact target/argv, revisions,
source/tool/dependency hashes, scope limits, reservations and complete axioms
are in each receipt. All successful top theorems have standard axioms only.
No Rust/Kani/ELF/full-manifest replay ran because covered source/artifacts did
not change and enclosing predecessors remain open. Existing adoption ELF pins
are retained, not claimed rebuilt or newly connected to these theorems.
