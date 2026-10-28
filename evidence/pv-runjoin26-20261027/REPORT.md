# Runjoin26 — LOG D333 resume

Target not yet established. Worktree exactly `/Users/dominic/ZK/.worktrees/pv-runjoin`; branch `codex/pv-runjoin-20261026`; entry HEAD `88b1a2ce97eb8d2711579678716b8fd3602f3cd9`. The lead correction is applied: generic consumers remain unchanged; the discharge route instantiates their source family at honest compiler inputs.

## 1. Exact honest-family handoff

`PV_RunJoin_HonestIdentification26.Honest` is exactly
`{i : PV_Src_NativeInput.Input // PV_RunJoin_ConsumerBoundary25.HonestInput i}`.
`inputs i := i.val`; `source_honest := PV_Src_NativeIdentification.prover inputs PV_Src_Transport.transport`;
`target := PV_RunJoin_UniversalBuild22.toInstance inputs admitted`.

The original three-field `BuilderSource.SourceIdentification source target` contract is unchanged, before and after:

```lean
public_eq : ∀ w : source.Instance,
  source.public w = BuilderSource.prover.public (target w)
build_eq : ∀ w : source.Instance,
  source.build w = BuilderSource.prover.build (target w)
transport_eq : source.transport = BuilderSource.π
```

Previously the attempted universal raw/admission-only instantiation had an unsatisfiable build field. Now `source.Instance = Honest`, and `identification` supplies all three fields without a remaining identification premise. This changes the chosen family, not the definition, fields, generic consumers, public projection, trace computation, transport, or conclusions. It does not assert that raw-family identification holds. The checked raw and admission-only `identification_unsatisfiable` theorems remain valid and are retained in the final audit.

For every honest input, `public_eq` reuses UniversalBuild22/UniversalPublic22. `build_eq` reuses UniversalBuild22's successful returned-bank law, universal returned-record/word/public correspondence, ForestBanks.merged_trace and ForestTrace.canonical_trace. These are the previously proved symbolic bank/late/append composition, not evaluation of a complete concrete run. The success guard retains BOTH Result layers: `@run E_shipped R_shipped i = ok (.Ok i.compiled)`, where R_shipped is UniversalRecords22.shipped with the canonical-root table. `transport_eq` reuses the existing D18 theorem. `transition` and `compiler_frame` instantiate UniversalTransition22 and UniversalCompilerFrame22 on every member of the same family.

## 2. Existing consumers and remaining endpoint boundary

`PV_RunJoin_HonestConsumer26` applies, unchanged:

- `BuilderSource.builder_refinement_D46_D51` → `source_sound`;
- `BuilderProtocolInstance.join_of_identification` → `protocol_join`;
- `BuilderProtocolInstance.builder_sound_of_join` → `sound_of_join`;
- `PV_Src_Consumer.of_identification` → `consumer` / `at_honest_input`.

All quantify over arbitrary statements/handles and bases supported by the original consumer. `at_honest_input` retains the matching-public guard. `canonical_fibre` supplies the EXACT `target i`, its matching canonical public and its trace equality for every honest i; it is not an unrelated existential witness.

**Discharged ledger scopes:** V152 (public), V153 (raw trace), V154 (S2 transport) at the lead-designated honest family. Three source-handoff P obligations are removed there. The consumer's identification argument is now a theorem, not a new assumed record. There is no residual universal successful-return/Checked/frontier premise outside the explicitly chosen subtype. No additional whole deployed ledger row is claimed closed.

**RustRealRefinement:** this closes its prerequisite builder/public/transport-to-canonical source handoff. It removes NO formal conjunct of RustRealRefinement and supplies NO `RunJoin` field by itself; that definition consists of the quantified Nonempty RunJoin obligation, not a builder subrecord. The actual endpoint fixes `input := BuilderSource.prover`, has no SourceIdentification argument, and still takes the same `RustRealRefinement template outputs x rust observer_program`. Its required common-sample complete ROMView/observer equality outside the fixed bad event (V038), concrete deployed rust/runtime/boundary association (V045), and same-coupling marginal laws are not established by initial trace equality. Complete proof/audit/observer/native effect and L1/L2/L3 associations remain obligations; source builder equality does not stand for them.

Endpoint premises removed/added/weakened: **0/0/0**. Intermediate generic contracts changed: **0**. Deployed P OPEN→OPEN; constructed P and prior 2/8/6 runtime/boundary record accounting are unchanged. T remains exactly entropy_law, entropy_kernel, observation. No T field added.

Recount5, quoted rather than silently rewritten: “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.” That was the historical residual; the NEW result closes the three source-identification fields for the honest family above, not all five generic native adapter premises on raw inputs or complete deployed execution. `ledger-input.json` pins the exact rows5 source and six relevant rows. Last supplied recount6 totals remain inherited: 407 rows, OPEN86, CLOSED-ON-CANDIDATE44, 400P/3T/4C. No fresh aggregate recount is invented; V152–V154 were recorded REDUCED scopes, so closing these three does not justify subtracting three from OPEN86.

## 3. Non-vacuity

`PV_RunJoin_HonestFixtures26.transfer` and `.withdrawal` carry the previously checked original full HonestInput proofs. Each instantiates public/build equality and the same existing consumer. `inhabited`, `transfer_fibre`, `withdrawal_fibre` check nonempty honest and canonical public fibres. `transfer_public`, `withdrawal_public` and `association` discharge both fields of the existing `PV_RunJoin_CanonicalFixtures.Association` at these ORIGINAL native compiler-return publics, reusing AdmittedCarrier23.public and CanonicalPublic21. These are V047 instance-level associations/non-vacuity; not arbitrary-x inhabitation or a P∧T native-world witness. No deployed byte decoder or runtime is inferred from these fixture witnesses.

## 4. Exact owner-facing scope of the privacy claim

The honest source handoff applies to EVERY user/prover input i carrying semantic Admission, a successful full compiler return equal to i.compiled (both Result layers), Checked, and canonical frontier words. For every such i, its native public and initial semantic trace equal those of the canonical `target i`, with the identical D18 transport. Selection is the honest prover's choice (D320); the theorem does not require generic consumers to exclude other families, or a deployment selector artifact.

Thus the intended honest-user privacy route is **privacy for users whose prover inputs are produced by the compiler and satisfy these explicit honest-input validity/representation guards**, universally over those inputs and the original adversaries/observations. It is not privacy for arbitrary caller-supplied cached compilations. Successful compiler provenance ALONE has not here been proved to imply all the other guards, and compiler totality on arbitrary malformed inputs is not claimed. The caller's compiler association is part of the chosen honest pipeline, not inferred from the spelling of `prover` or from matching public data.

This family choice does not restrict the adversary, weaken the observer/simE, change the bound or bad event, or discard/condition runtime retry and abort observations. Those still require their original complete-experiment refinement. This work proves the builder handoff needed for that privacy route; it does not by itself prove RustRealRefinement or release privacy. The raw padding counterexample concerns a family containing non-honest inputs and does not refute this subtype theorem.

## 5. Validation and stop

5/64 charged host Lean attempts, 4 accepted and 1 rejected; 0 Kani, 0 local Lean. Accepted: 38135 HonestIdentification26, 38137 HonestConsumer26, 38138 HonestFixtures26, 38140 HonestAudit26. The 24 new theorems all have accepted #print axioms, restricted to propext, Classical.choice, Quot.sound. The final audit additionally prints the exact source family, three-field contract, generic consumer, fixture Association, endpoint and RustRealRefinement types, and rechecks the raw-family unsatisfiability and endpoint axioms. Current four new modules match accepted source snapshots and git blobs.

38136 is a retained, ordinary syntax rejection: local notation K required quoting the named field parameter as «K». The corrected source passed 38137; this failure is not a stop. 38139 was refused BEFORE launch (reservation projected 59,995,324,416 bytes over the 59,055,800,320-byte limit), retired with zero charge, and retried after the required three minutes with new ID38140. No timeout, memory kill, cap increase, unchanged failed resubmission or transport retry. Audit IDs38194–38196 were already spent by runjoin24 and were NOT reused; inherited-id-use.json records the receipts. Remaining budget59 Lean/0Kani; unused authorized focus IDs38141–38193 (53 IDs). Stop is removal, not exhaustion.

All scopes sequential MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000. Peak RSS5,017,350,144bytes, every swap0. receipt-index.tsv and receipt-*.json record each exact target, exit, host wall time, peak RSS, swaps, revision/blob/source sha256, command, dependency fingerprint and full axioms. Source snapshots and rejected output are retained.

Before the first compile, all5673 actual selected external objects matched h4/SCOPE; external-manifest-authority.json verifies the inherited manifest equals the official pinned replay authority. The actual final proof/audit closure resolves1385 project modules with no unpinned module, using EJR/freeze/h5 and h5-prime precedence; tracked variant conflicts are recorded in focused-resolution.json. Final private cache source checks match all1385 modules. h6 checks669 reused replay roots,785 complete transitive source/object fingerprints and the unchanged toolchain, all matching. Private retained cache only; no shared source or another job's objects written. This is focused compilation/dependency/axioms evidence, not a fresh coherent release rebuild or a full manifest replay.

An EXTRA read-only resolution of PV_RunJoin_Endpoint as a wider audit root was stopped under h4/h5 for six unpinned modules: AspisR1CircleFallback.RawCircleFallbackOutputBridge; AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4; AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyV2; AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1; ProverRwSampler.Funs; R1Z.ProverRwFullFuns. No compile/substitution of these was attempted. wider-endpoint-boundary.json retains the exact finding. These are not imports missing from the successfully resolved and audited honest-family/actual named endpoint closure; they do not block the requested builder handoff. The remaining full runtime instantiation still needs its own coherent source-authority resolution.

commits.txt records the path-limited proof-stage git log from entry HEAD; the final evidence commit follows. Stop is the completed removal of V152–V154 at the authorized honest-family discharge route, after consumers, both non-vacuity instances and reporting are checked. The ordinary rejected candidate is retained and is not the stop reason. No shipped-source, simulator, observer, binary, wallet or key change; no push or merge.


## Next concrete deliverable

Use this closed honest-family source certificate at the complete native execution handoff: for each honest i and matching public, establish the concrete caller/runtime/body/world and full observable RunJoin agreement at canonical target i, retaining the existing bad event, marginal coupling, observer and three trust fields. V038/V045 and the corresponding native/side-channel obligations remain; no additional builder-identification proof on the raw family is appropriate. The lead can record V152–V154 as discharged at the intended honest family and the owner-facing scope in §4.
