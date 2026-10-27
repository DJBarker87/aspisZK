# TX1 query/flush/writer accepted-execution handoff

Branch `codex/cx-tx1-query-20261025`. **Partial checked delivery. S2 and the
100-bit target remain open; unconditional TX1 frozen2/native-writer closure
is not established.** No shipped-source counterexample was found or claimed.

## Exact checked result

`lean/Tx1Q_Accepted.lean`,
`AspisR1.Tx1Q_Accepted.accepted_pair_claims_tx1`, specializes
`Op4P_Accepted.accepted_pair_claims_op34` and destructures its accepted pair
once. It retains every original conclusion for the SAME f,s,cuts,saved,outer
and native accepted executions. It additionally constructs `Tx1Q_Execution.Run`
from that TX1's actual preparation suffix, including its own Prepared,
gamma scratch, initial accumulator, batch call/root, geometry, pending rows,
query return, flush and writer call. These are outputs of success inversion;
no SourceCuts, second successful TX1, chosen query return, flush success,
writer success, or state-provenance witness is added as a premise.

CurrentCaller slots **7/17/16** correspond to VTop **6/9/8**. The actual base
uses CurrentCaller, so installing by the VTop numbers would be incorrect.
`Tx1Q_Carriers` supplies content-preserving nominal maps and checked K/E,
accumulator and pending roundtrips. Prepared maps every field explicitly.
`Tx1Q_PrefixInstall` also installs the initial/pending/geometry helpers needed
to derive the run. `other_slots` restores precisely those six CurrentCaller
fields; op3/op4 and the existing Claims/preparation installation remain intact.

Unconditional on additional arithmetic/model hypotheses, that SAME run has:
reservation=true, split=10, next=10, 64 flushed weights, canonicality of all64
flushed weights, and saved equal to the selector writer reference output on
that exact materialized state (`Tx1Q_Control.fields`, `Run.writer_call`).

`Tx1Q_QueryBridge.query_body` proves total Q1 body compatibility, and
`Tx1Q_Q2Bridge.{query,flush,writer}` proves total slot compatibility with Q2's
explicit installation and chosen Q1 leaf instance. The Result factor covers
outer failure/divergence and both Rust outcomes. This is a bridge for the
three requested slots, not equality of arbitrary whole dictionaries; Q2's
other slots are not silently installed into the accepted pair.

`Tx1Q_Model.ten` and `Tx1Q_Endpoint.WhenBound` give the success-conditioned
frozen2 model-state equality and SAME saved writer output, using the run's own
Prepared/geometry/scratch/query/flush. The model is
`OraclePortCheckpointResumeC5.model data rho q`; the conclusion is exactly
`CheckpointBytes5Output.accumulator materialized = (write model).accumulator`.
`WhenBound` is explicitly conditional on the remaining gates listed below.
It is printed in receipt028; it is not presented as premise discharge.

## Premise audit and remaining local gates

`before-statement.lean.txt`, `after-statement.lean.txt`,
`specialized-before-statement.lean.txt`, `new-conclusion.lean.txt`, and
`premise-audit.json` audit the COMPLETE statements. Removing only the new
existential run/conclusion from the after statement yields byte-for-byte the
consistently specialized Op4P statement. Added parameters are CoreError,
reserved, queryOps and geoOps; no new top-level logical hypothesis. This
restricts an arbitrary dictionary family to the explicit helper/reference
instance; it does not establish equivalence to every old dictionary. The
conditional model gates are new conclusions under implication, not claimed
removed assumptions. All original SDK/std/allocator/runtime/extraction/oracle,
child marks, checkpoint/history, P2Prime and other conditional cone premises
remain. No cryptographic assumption, failure event, security metric, source
version or release target is changed.

| Gate | Disposition on this accepted run |
|---|---|
| SAME preparation/query/flush/writer, initial/pending success, split, reservation, raw/vector sizes, next | Derived by suffix inversion, concrete slot equations and source row/flush proofs. No independent run. |
| Q1 wire length | Derived from the installed Op3I header in the top theorem (also already a SourceCuts field). No length premise in `WhenBound`. |
| Parsed wire identity | Derived from `parseReached` when that remaining parser/transcript gate is supplied; never a separate arbitrary wire premise at the endpoint. |
| ROM/opening/geometry access | Q1 opening and forQuery slots are concrete; actual geometry call yields its range binding under the named domain/geometry owners and mul/one/inverse laws. Those named owners remain explicit. |
| SessionAPrepare / SessionAPrimitives and primitive arithmetic laws | Retained on the run's own Prepared and query dictionary. No independent Prepared is chosen. Their concrete owner instances are not certified here. |
| Line canonicality | NOT discharged: it remains the existing `SessionAPrimitives.line_canonical` field. Query op16 is still an owner primitive; a decoded-field line equation does not imply raw limb canonicality. The concrete source line/backend canonicality proof must instantiate this field. Packing it in SessionAPrimitives earns no extra closure credit. |
| `parseReached stored tr = some parsed` | NOT discharged: op3/op4 prove header and full physical scan, while frozen2 still needs semanticRows27 and Aligned for the SAME source transcript. Actual Claims prefix success alone does not supply these distinct statements. |
| `LiteralMatchingData.read (typedRows parsed q tr) = some data` | NOT discharged: needs the actual parser/absorbed-row/transcript-to-data refinement. SessionAPrepare relates the returned Prepared to a supplied data value but does not prove this read. |
| Indexed selected-map authentication | NOT discharged: CurrentCaller batch op6 (VTop op5) is intentionally still the base batch slot. Its successful unit return alone cannot authenticate `recovered (index q 2 pos)` for all22 positions, particularly across both batches. No Op5T or Tx2Q result is imported or awaited. |
| Q2 ObservationBinding | Not assumed. Direct Q1 bounded observations and induction prove the ten-step conclusion; a stronger unbounded global ObservationBinding is unnecessary for this endpoint. |
| Native writer admission | NOT discharged: the installed Lean body is explicitly `Port3_CheckpointInstall.writer`, Q2's SELECTOR REFERENCE. We derive 64 canonical weights, next10 and the actual writer arguments; we do not yet derive S2/immutable WideExact canonicality on this Prepared, public1880 and the full caller/carrier/runtime admission required by the bounded native certificate. No total native equality is claimed from a reference identity. |

The inherited D188 native association is retained at the specialized dictionary.
Specializing it to a selector writer does not itself prove that the shipped
native writer satisfies its bounded P6 domain. This remains an implementation
refinement obligation, not a cryptographic assumption. Query/flush source-body
associations likewise retain their existing extraction/P6/runtime boundaries.

Next concrete deliverable: instantiate source line canonicality and the
same-return immutable Prepared owner fields; bind the actual semantic rows
and transcript to `parseReached`/matching data; compose the merged batch owner's
indexed authentication on this SAME run; then consume the native writer's
bounded certificate on the now-derived input guards. No new agreement or
whole-result hypothesis should replace these proofs.

## Non-vacuity

`Tx1Q_Nonvacuity.extraction_satisfiable` constructively inhabits the same
specialized D188 association for arbitrary remaining dictionaries.
`initial_pending` exhibits the concrete successful constructor and pending
allocation prefix. These exclude a contradictory new association or an
always-rejecting local allocation installation. They do NOT provide a new
joint native/runtime/crypto accepted-pair fixture, nor prove joint
satisfiability of every retained model/owner gate. The accepted theorem is
success-conditioned; that distinction is deliberate and audited.

## Validation, trust and frozen artifacts

`validation-summary.json` indexes every exact command, target, source revision,
source SHA256, exit status, wall time, peak RSS, swap and full printed axiom
lines. Each raw receipt also pins direct dependency objects, Lean binary,
LEAN_PATH, actual cgroup and enforced limits. `final-host-pins.json` records
new object hashes/sizes, inherited coherent manifests, Q1/Q2/Op4P root objects,
and unchanged launcher hashes, without committing any binary.

| Final target | Attempt | Exit | Wall s | Peak RSS KiB | Swap | Source anchor |
|---|---|---:|---:|---:|---:|---|
| Tx1Q_Accepted.lean | 025 | 0 | 2.170188711 | 5,182,436 | 0 | 30f7e6bdd0 + dirty source hash |
| Tx1Q_Nonvacuity.lean | 027 | 0 | 1.957200987 | 5,188,364 | 0 | 30f7e6bdd0 + dirty source hash |
| Tx1Q_Audit.lean | 028 | 0 | 1.902580400 | 5,152,204 | 0 | 30f7e6bdd0 + dirty source hash |

The final source bytes are committed in `1cffb07b2d` and match passing receipt
hashes for all15 new modules. `#print axioms` for the accepted theorem is
`[propext, Classical.choice, Quot.sound]`; the final audit checks all38 new
theorems, with only subsets of those standard axioms. It also prints Run,
Slots, WhenBound and retained preparation/primitive structures. Failed
elaborations with diagnostic sorryAx are retained but excluded from successful
proof evidence. Final sources contain no sorry/admit/new axiom/native_decide,
heartbeat/depth override or unsafe reducibility option. `git diff --check`
passes. No package/full-manifest replay was run or claimed.

Budget used: **28/80 actual Lean compiles, 0 dependency builds, 0/40 Kani**.
There was also one failed preflight before Lean spawned (conservatively29/80
if counted): a dependent Cuts attempt was submitted before its PrefixInstall
predecessor had compiled. The launcher correctly reported
`FileNotFoundError: Tx1Q_PrefixInstall`; the predecessor was fixed first.
`preflight-failure.txt` records that rejected invocation. No launcher/build or
monitoring infrastructure was built or repaired.

Every actual compile used the unchanged S2W launcher in its own capped host
scope, `lake env lean -j1 -M7000 -DElab.async=false`, MemoryHigh6G,
MemoryMax8G, MemorySwapMax0, TasksMax64. This worker reserved only one8GiB scope
at a time; all its jobs are terminal. Final host inspection showed only
init.scope. There was no memory kill, cap increase or wall-timeout rerun.
008/010/011 hit the unchanged default Lean heartbeat limit at whnf; each
successive source changed the proof factorization, and014 fixed the reduction
graph by keeping the large current TX1/preparation bodies opaque. No heartbeat
limit was raised. Other failures are retained syntax/type/elaboration checks.

Host reuse was coherent SInt2/Op4P first, followed by the existing unchanged
Q1/Port4 and Q2 object caches. No existing proved module or object was edited.
This is focused cached composition, not a fresh coherent release rebuild.
`writer-source-check.json` verifies **173/173** current source/dependency pins
against Q2's admitted native writer packet. It reuses Port3 Kani001 and encode
contract002; no unchanged Kani gate was rerun. Source identity alone does not
supply the missing input-domain proofs above. No Rust/SBF job was launched.

Only new Tx1Q_ modules and this receipt directory changed. No shipped file,
cfg(kani) harness, feature, protocol parameter, wire format, key, account,
release artifact, session A worktree or S1/S3/S4/S5/S6/S9 candidate was changed.
The ELF rebuild trigger did not fire. Inherited pins, NOT newly reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Stage commits are local; no push or merge. No binaries, objects, ELFs or
archives are committed. Runtime/oracle histories, rejected prefixes,
cross-checkpoint state, FinishOps, source-to-ELF and the security headline
remain outside this conditional endpoint, as in the inherited S2 handoffs.
