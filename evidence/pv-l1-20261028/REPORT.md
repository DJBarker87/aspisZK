# L1 counts and errors: final handoff

Branch `codex/pv-l1-20261028`, exactly `/Users/dominic/ZK/.worktrees/pv-l1`.
Base `1e826627aa39fe02569bf840efb894eaa287efcf`; authorized runjoin tip
`c6a2b73cc0` merged without conflicts at `0a97bf0d6b`. No push.
**V347–V351 all remain OPEN/P. No privacy endpoint or deployment premise was
removed. The target is not established.** Budget exhausted: 100 Lean compiler
invocations, IDs 51600–51699 inclusive; zero Kani invocations.

## Checked results and their limits

These are Lean emission/model results, with standard axioms only, **not native
execution associations or structural (K-1 substitute) gates**.

* `PV_L1_EntropyProducer.source_replay` invokes the supplied-tape source owner,
  obtains its replay, retains exact status and final tape, and derives ordered
  RNG call/return tags from the consumed tape interval. `PV_L1_EntropyCounts`
  derives exact indices, return statuses and counts, bounded by sixteen. Raw
  seed bytes are excluded from the observation. The existing concrete
  `ProverRwRngTape.concrete_zero_then_one` fixture concerns this source model;
  it is not a native honest execution witness.
* `PV_L1_QueryProducer.complete_result` erases to the literal emitted query
  caller, preserving the entire Result and state. `completed_order` and
  `PV_L1_QueryRecord.of_source/abort_record/digest_count` show one absorption
  digest followed by sixteen eager block/advance digests, in order, on every
  completed outer Result, including inner `Err Transcript`. This counts digest
  entries, not every word/scan instruction or native ROM/TLS/world event.
  An outer failure/divergence retains its prefix through Logged bind; the
  seventeen-entry theorem does not assert completion for such executions.
* `PV_L1_SamplerJoint.complete_joint_kernel/scalar_joint_kernel` use pv-l2b's
  simulator laws to equate a finite IID-coordinate source kernel and simulator
  kernel for an arbitrary test of the SAME (draw count, value/error) outcome.
  `simulator_mass_one` proves normalization for `Fin p`, `p > 0`. This is not an
  instantiation of the native RNG/hash kernel, mask/TLS/oracle history, or simE.
* `PV_L1_CanonicalSource.transfer/withdrawal` use the runjoin successful
  canonical-preparation theorem to obtain an honest original input and an
  emitted Result-erasure law at that input's nominal public and original
  compiled payload. They add no independent honesty assumption. The law holds
  for every input; it is **not** a side-channel simulation theorem. Source070
  still calls the full prover body opaquely.
* Thirty-nine generated phase interpreters have complete Result-erasure laws.
  Phase-entry markers do not establish actual native observer events. The
  retry helper `PV_L1_NativeProducer.native_eq_model` interprets two distinct
  Result boundaries with arbitrary leaf prefixes; despite its name it is only
  a control-model equality. Callback errors escape; only prover Rejected retries.

## Per-row before and after

| Row | Before | After / theorem evidence | Evidence class and non-vacuity |
|---|---|---|---|
| V347 native event producer | OPEN/P: native counts/errors not produced by D163 event owner | OPEN/P: entropy source replay/counts, phase erasure and canonical source applications above; full body and native association open | Emission/model. Source replay permits success, exhaustion/rejection and OS-error tags with exact returned state. Canonical theorem assumes actual preparation success, not a newly postulated honest-input predicate. No native honest witness supplied. |
| V348 joint mask/count/TLS/oracle | OPEN/P: complete same-run joint simulation absent | OPEN/P: SamplerJoint kernel equality and normalization only | IID-coordinate model. Counts, accepted values and exhaustion remain joint under arbitrary test; p>0 supplies a nonempty value space. Native failure independence and joint simE instantiation absent; no marginal substitution or new bad-event allowance. |
| V349 equal-circle integration | OPEN/P: full honest native error prefix absent | OPEN/P: Source067 erasure retains emitted error paths; no equal-circle simulation established | Emission/model only. EqualCirclePoints remains fatal Semantic; ActivePole remains retrying Rejected. No native honest equality/pole execution or leak witness established. |
| V350 query-abort integration | OPEN/P: eager reads/abort prefix not integrated | OPEN/P: QueryRecord proves exact completed source prefix of seventeen digest entries, also for inner Err Transcript | Emission/model. Inner errors are retained rather than conditioning them away; ordinary completed output can be an error. Native ROM/TLS association, scan counts and same honest full-run instantiation remain open. |
| V351 part47 composition | OPEN/P: native owned-reference image/event binding absent | OPEN/P: retained prior owned-reference image plus partial emitted prefix laws | No new native evidence. No native part47 image or honest instance constructed; no byte-image equality inferred from phase annotations. |

No checked honest-native secret-dependent counterexample was obtained. This is
not a proof that no leak exists; compile errors and model-only fixtures are not
native counterexamples. No count/error outcome was silently removed.

## Explicit retained hypotheses

`V163_native_body_data`: the original complete proof/audit data association,
`data execute = model` at `ProverRwP6BodyData.refinement_of_data`, remains an
OPEN native hypothesis. No replacement association is claimed here.

`V167_native_effects`: native ordered ROM/TLS effects, failed/diverging prefixes,
Drop/unwind/world and returned-state association with the selected source/event
model remains an OPEN native hypothesis. This job does not duplicate runjoin's
native-association work or discharge that hypothesis by renaming an event map.

Before/after: privacy headline and deployment conditions unchanged. Trust T stays
exactly `entropy_law`, `entropy_kernel`, `observation`; none removed, added,
weakened, or hidden in T. Observer and simE unchanged. D163's model theorem is
retained, not promoted to a native theorem.

## Validation and source authority

`validation-summary.json`, `attempts.jsonl`, and every `receipt-516xx.json` retain
exact target, exit, host wall time, peak RSS, swaps, source revision/blob/hash,
input dependencies and axioms output. 67 accepted invocations, 33 failed; all
failures and their source snapshots retained. 57 accepted new modules including
three audits; 72 new theorem statements. Final audits 51697/51698/51699 all
passed. Peak RSS 5,147,500,544 bytes; swaps zero; total capped-command wall time
233.37 seconds. Scopes used MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0,
TasksMax 64, Lean -M7000; no caps raised. One scope at a time. No local Lean,
Rust arithmetic gate, extraction, native differential, Kani or release ELF build.
This is one final focused manifest replay, not a full frozen privacy release.

All 5,673 h4 external objects verified before compiling. Final h6 reuse verified
1,953 selected project sources/objects and complete dependency fingerprints.
The final read-only audit checked 7,700 hash paths and inventoried 2,020 own-view
objects; no mismatches or other-job ID collisions. No XR import. No edits under
crates/ or programs/, soundness files, shared build infrastructure, or another
worktree. No wallet/key actions. `cleanup.json` records removal of only this
job's objects and external links; sources and evidence remain on the host.

The final common-rulings snapshot includes (x), feature parity, and h7. Under
(x), deployed client features/profile/body parity were not verified; **all
native/deployed-code credit is zero**. No Kani PASS was consumed or re-credited;
K-1/K-2 quarantines and copy/contract/static-route restrictions remain intact.
The focused resolved module keys do not import the h7 ambiguous extraction
examples; text mentions alone do not resolve a module. EJR/freeze precedence and
h5/h6 selected cohort were retained.

## Stopped proofs and next deliverable

`final-source-manifest.json` separates 39 accepted generated modules from 34
unaccepted generated drafts; `draft-status.json` also includes the diagnostic
module. Drafts live as `.lean.txt`, outside the importable Lean tree. They have
zero theorem credit. `accepted-theorems.json` is the exact audited list.

Source069 (full `prove_masked_with_attempt`) needs a typed prefix/tail split;
its unchanged large symbolic proof was not rerun with larger caps. The
Source070 opaque body cut is explicit, not completion. Source071 retry erasure
is unproved. Last focused attempt 51696 exposed a double `Logged.lift` around
the already-logged concrete query producer in Source020; it is preserved as a
failed draft and gives no caller-composition credit. Earlier publish_compact
heartbeat failure was replaced by a changed symbolic tuple projection proof,
recorded in `heartbeat-replacement.json`. Own-input errors are recorded in
`input-correction-51654.json` and `input-correction-51671.json`.

Next: fix the Source020 logged-call composition, split Source069's tail into
small typed complete-Result/event lemmas, then compose the retry/part47 producer
with the existing D163 coupling on canonical honest inputs. A native row closure
also needs the deployed-feature fidelity checks, same-input finite validation
where required, and named open V163/V167 associations supplied by runjoin.
No additional compiler attempt is authorized by the exhausted budget here.
