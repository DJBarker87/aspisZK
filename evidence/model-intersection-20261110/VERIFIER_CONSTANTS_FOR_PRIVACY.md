# Verifier-side constants the privacy theorem should depend on (one model with soundness)

For: Stream B (privacy). From: the Stream A lead, read-only. Repository /Users/dominic/ZK, branch research, 2026-11-10. No build ran and no source changed.

## 0. Basis and method

- Soundness top: `AspisR1.TAS_FinalB.deployed_splitB` and `deployed_charge` (evidence/integrate-20261111/TAS_FinalB.lean). Kernel statements are in TAS_G0_AUDIT.json `kernel_statements_verbatim`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. The status field reads "top assembled UNCONDITIONALLY at the corrected host (G0 FINAL, run 7); target not yet established".
- Host: `S := AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L0 copy std` (evidence/a1x-20261108/NOC_Run5bHost.lean). The namespace `AspisR1.NOC_HostSeed` is defined inside that file; there is no separate NOC_HostSeed.lean.
- Cone membership: every name marked "in cone" below was checked by exact-line match against the pinned splitB reachable list (evidence/replay-l187-20261109/final/L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz, 146,370 constants).
- Provenance: from evidence/prov-p6r-20261110/PCXD_PROVENANCE.json (P6 refresh, frozen source 4bb3b3f, ledger30 gate), with a spot check of the newer prov-p3h-20261110 handoff (PCVH). "Gate module" means the Lean module that defines the constant in the ledger30 build. PCXD kinds are FROZEN_CRATE (the emission header names a frozen crate), PROBE_OR_CUT_CRATE (an Aeneas emission of a probe or cut crate) and TRANSFORMED_COPY / REFERENCE. Statuses are RECEIPTED, EQUALITY_PROVED, OPEN and HAND_ADAPTED. "NOT_IN_PROVENANCE" means the name has no PCXD definition record: either it is unannotated hand-written code, or its module is not one of the 373 emitted gate modules.
- Correction to the brief's spellings: several names carry an `AspisR1.` prefix that the brief left out. They are `AspisR1.DrvC_Installation.*`, `AspisR1.NNH_S1HostCodec.*`, `AspisR1.NOM_TerminalDomain.*`, `AspisR1.NOC_HostCtx.*` and `AspisR1.FJn_BeginCanonical.*`. Others have no prefix: `NNH_S1DecodeOk.*`, `NNH_ReturnsBundle.*`, `NNH_Tx1Returns.*`, `NNH_Libraries.*`, `NNH_ExactRemainingTypes.*`, `NNH_CorrectConfiguration.*`, `NOC_Stage1Forward.*`, `NOC_Stage1Conv.*` and `LIB_VPublicDomain.*`. The spellings below are the ones in the sources and the cone.
- Main finding, which affects the recommendation: **none of the verifier-body definitions below has a closed provenance status against 4bb3b3f.** They are Aeneas emissions in the gate, but PCXD records each one as OPEN. "The verifier" in the soundness theorem is therefore "the gate's extraction", not yet "4bb3b3f proved equal". This is Stream C's open obligation, and it applies to Stream B unchanged if Stream B adopts these constants.

## 1. Classification summary (what is "the verifier" and what is "the reference")

| Role | Constants | Origin |
|---|---|---|
| Verifier body (Aeneas emission in the gate) | `AdapterRw.r1_pool_adapter.owned.stage1_owned`/`stage2_owned`; `AspisR1CurrentCaller.verifier.candidate.tx1`/`prepare`; `VTop_Stages.verifier.candidate.tx2_common`/`tx2_authenticated`; `AspisR1PublicPreparation.r1_wire.begin`, `r1_semantic.public_transcript`, `r1_wire.SemanticTranscript.semantic_validated`, `sampler.qm31_sample`; the three sampler extraction modules | Aeneas output. Every one is PCXD OPEN (none RECEIPTED or EQUALITY_PROVED). The samplers and AspisR1PublicPreparation come from probe crates, not the frozen crates |
| Installation and wiring (hand-written) | `AspisR1.NOC_HostCtx.sdk`/`configuration`/`model1`/`model2`; `AspisR1.DrvC_Installation.*`; `AspisR1.FIp_Install.configuration`; `NNH_CorrectConfiguration.sdk`; `AspisR1.NOC_HostSeed.m0`/`filled`; `AspisR1.NNH_S1HostCodec.validate`/`encode`/`install`; `NNH_S1DecodeOk.carrier` | Hand-written Lean dictionaries and literal slot fillers that install emitted functions into the `Ops` records. `NOC_HostSeed.filled` is a hand model of heap.rs `filled` |
| Boundary-parameterised verifier models | `AspisR1PublicPreparation.VerifyPrefix.verify`, `RoundModel.rounds`, `FinishModel.finish` | Not Aeneas-headed. They are copies of the emitted verify/rounds/finish with callee calls abstracted into `Boundaries` records (2026-10-17 bridge directories). They have no PCXD record |
| Reference (RSL / library, hand-written spec) | `RSL.TX1_345.Ref`, `RSL.TX1_345.S1Lib`, `RSL.TX2_241.Ref`, `RSL.TX2_241.V2Lib`, `RSL.TX2_241.Dom064`; `NNH_Libraries.{VL,P,C,L,D,V0}`; `LIB_S1.library`; `NNH_Tx1Returns.value`; `NNH_ReturnsBundle.tx1Value`; `LIB_VPublicDomain.*` | Hand-written models of the frozen Rust (RSL row specs and LIB evaluators) |
| Equivalence theorems (verifier = reference) | `AspisR1.NOC_Stage1Iff.iff345`, `NOC_Stage1Forward.ok345`, `NOC_Stage1Conv.conv`, `AspisR1.NOF_Tx2Op11.tx2Op11`, `AspisR1.NOF_A2FieldCorrected.field`, `AspisR1.NOQ_FinalCombined.field`, `AspisR1PublicPreparation.SamplerTransport.sample_eq` | Proofs. They add no axioms beyond the standard three |

## 2. (a) Accept predicate on proof bytes and public inputs

### 2.1 Installed stage entries (the verifier as the soundness theorem sees it)

`AdapterRw.r1_pool_adapter.owned.stage1_owned` (in cone). Gate module: AdapterRwModel. The copy read here is docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:2857, whose header is "AUTOMATICALLY GENERATED BY AENEAS, [aspis_r1_cost_probe_program]".
```lean
def r1_pool_adapter.owned.stage1_owned (ops : Ops)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
```
This is the TX1 program entry (`stage1_owned` in r1_pool_adapter_owned.rs). It returns the saved afterstate bytes on Ok. PCXD records it as FROZEN_CRATE, OPEN, NOT_COVERED ("no verified common declaration with a text-identical receipted frozen emission"). The module note says "Aeneas output hand-parameterised by `structure Ops`".

`AdapterRw.r1_pool_adapter.owned.stage2_owned` (in cone). Same module, line 3326.
```lean
def r1_pool_adapter.owned.stage2_owned (ops : Ops)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  Result (core.result.Result Unit solana_program_error.ProgramError)
```
This is the TX2 program entry. It accepts with `Ok ()`. It has the same PCXD status as `stage1_owned` (OPEN, NOT_COVERED).

The installed host projections (evidence/a1x-20261108/NOC_Run5bHost.lean, namespace `AspisR1.NOC_HostCtx`, all in cone; written by hand):
```lean
abbrev configuration {W Tx : Type} (c : Ctx W Tx) :=
 FIp_Install.configuration c.fixed.indexError (base c) c.fixed.reservation
abbrev sdk {W Tx : Type} (c : Ctx W Tx) := DrvC_Installation.sdk (configuration c)
abbrev model1 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.First :=
 AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c)
abbrev model2 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.Second :=
 AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk c)
```
`model1` and `model2` are what `S_host.model1` and `S_host.model2` are. `base c` uses `missing c := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 (envOf c).reservation) (envOf c)) (envOf c)`, which is a literal substitution with no binder. The types come from docs/research/100bit-spend-path-20261013/lean/S2W_ExtractionBoundary.lean:16-17:
`abbrev First := Program → Accounts → Slice U8 → Result (core.result.Result (alloc.vec.Vec U8) Cuts.PE)` and `abbrev Second := Program → Accounts → Slice U8 → Slot → Result (core.result.Result Unit Cuts.PE)`.

A form that does not need a `Ctx` is `NNH_CorrectConfiguration.sdk` (evidence/integrate-20261111/NNH_CorrectConfiguration.lean:17, in cone, hand-written):
```lean
def sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2Configuration.sdk (residual missing env) env err reserve
```
`AspisR1.NOF_A2FieldCorrected.sdk_at_slot` and `AspisR1.NOC_Stage1Iff.sdk_at_slot` (both in cone) prove
`NNH_CorrectConfiguration.sdk (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation) (NOC_Run5bCtx.envOf c) c.fixed.indexError c.fixed.reservation = NOC_HostCtx.sdk c`.
So the installed verifier depends on the context only through `env`, `indexError` and `reservation`. This is probably the simplest constant for a privacy statement to quantify over.

Seed (same file, namespace `AspisR1.NOC_HostSeed`, hand-written):
```lean
def filled (reserved : Bool) {T : Type} (_copy : core.marker.Copy T) (n : Usize) (x : T) :
    Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error)
def m0 (reserved : Bool) : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE
```
`filled` is described in the source as a "Faithful model of the frozen `aspis_core::r0::heap::filled` (heap.rs:5-10 at 4bb3b3f)". `m0` is `NNH_HostSeed.m0` with `currentBase.op1 := filled reserved`.

### 2.2 Configuration and installed dictionaries

`AspisR1.DrvC_Installation` (/Users/dominic/ZK/lean/DrvC_Installation.lean, hand-written; `currentInstalled`, `sdk` and `stage` are in cone):
```lean
structure Configuration (F CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  finish : AspisR1Stage2.Stage2Finish.FinishOps F
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError
  boundaries : AspisR1PublicPreparation.FinishModel.Boundaries
  std : ClaimsUnrolledFinish.StdCalls
def stage (c : Configuration F C) :=
  DrvI_Installation.stage c.reserved c.query c.geometry (AuS1_Install.base c.stageBase) c.finish
def currentInstalled (c : Configuration F C) :=
  RowShape_InstalledSlots.verifierOps (current c) c.boundaries c.std
def sdk (c : Configuration F C) :=
  DrvI_Installation.sdk c.adapter c.currentBase c.reserved c.query c.geometry
    (AuS1_Install.base c.stageBase) c.finish c.boundaries c.std
```
`currentInstalled (configuration c)` is the installed TX1 verifier dictionary. Its `op9` is the semantic verify (see `NOC_Op9Slot.slot` in section 4) and it is the `ops` argument of `verifier.candidate.prepare` (`NOC_PrepareFront.cur`). `AspisR1.FIp_Install.configuration` (/Users/dominic/ZK/lean/FIp_Install.lean, hand-written, in cone) has the signature `def configuration {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) := Rc5_Install.configuration err (select r c) r`.

### 2.3 Candidate verifier functions (emitted)

`AspisR1CurrentCaller.verifier.candidate.tx1` (in cone). Gate module CurrentCompactCallerModelV1. The gate copy is evidence/prov-p3h-20261110/inputs/gate_CurrentCompactCallerModelV1.lean:312, header "[aspis_r1_cost_probe]".
```lean
def verifier.candidate.tx1 (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
```
This is the TX1 verifier (`verifier.rs`, candidate `tx1`). On acceptance it returns the checkpoint bytes. PCXD: FROZEN_CRATE, OPEN, NO_FRESH_EMISSION.

`AspisR1CurrentCaller.verifier.candidate.prepare` (in cone). Same file, line 194.
```lean
def verifier.candidate.prepare (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (proof : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit))
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
```
This is the TX1 prepare front: it parses, builds the transcript and derives the prepared challenges. PCXD: OPEN, NO_FRESH_EMISSION.

`VTop_Stages.verifier.candidate.tx2_common` (in cone). Gate module VTop_Model (evidence/prov-p3h-20261110/inputs/gate_VTop_Model.lean:180, "[aspis_r1_cost_probe]").
```lean
def verifier.candidate.tx2_common (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
```
`VTop_Stages.verifier.candidate.tx2_authenticated` (in cone). Same file, line 300, with an identical signature. It is the TX2 authenticated verifier (`ops.op3 proof` parse, then the common continuation); the TX2 SDK entry `op11` is this function over the installed stage (`NOF_Tx2Op11`). PCXD: both OPEN, NO_FRESH_EMISSION. PCVH lists a "VTop_Model generator repair" as next work.

Also in the cone, as callback-parameterised emissions used in the A1 proof chain:
- `NMT_tx1.verifier.candidate.tx1`: evidence/tx1-owned-20261111/NMT_lean/NMT_tx1/Funs.lean:165. It has twelve callback parameters `NMT_call_0 … NMT_call_11` followed by the same tail `{H} (aspis_coredigestDigest32Inst) (public1) (public_bytes) (proof) (k) (hash) (obs) : Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)`. PCXD: FROZEN_CRATE, OPEN.
- `NMP_prepare.verifier.candidate.prepare`: evidence/tx1-observed3-20261110/NMP_lean/NMP_prepare/Funs.lean:257. It has `NMP_call_0 … NMP_call_11` callbacks followed by the prepare tail above. PCXD: OPEN, WRONG_BASIS.

The installed path (`DrvC_Installation.currentInstalled`, `NOC_PrepareFront.source`) uses the `AspisR1CurrentCaller` versions.

### 2.4 Library references the entries are proved equal to (hand-written)

`NNH_ReturnsBundle.tx1Value` (evidence/integrate-20261111/NNH_ReturnsBundle.lean, in cone):
`abbrev tx1Value := NNH_Stage1RefEval.value VL P NNH_Tx1Returns.values C`. This is the total evaluator of `RSL.TX1_345.Ref VL P C` (by `tx1_returns`, it includes the Err arms).

`NNH_Tx1Returns.value` (evidence/integrate-20261111/NNH_Tx1Returns.lean, in cone):
`def value (a : TX1_094.Args V) (env : Env) : Except V.VErr Bytes`. This is the TX1:094 verifier-tx1 evaluator, a chain of split check, parse shape, canonical scan, prepared, batch Merkle, geometry, query loop, finish and checkpoint. `V := LIB_Instances.VL` and `P := LIB_Instances.P`.

`RSL.TX1_345.Ref` (evidence/integrate-20261111/NNH_dependency_inputs/RSL_TX1_345.lean; in cone):
`def Ref (V : VLib) (P : PreparedNew V) (C : S1Lib V) (a : Args) : RS Bytes`. This is the row spec of `stage1_owned`.

`RSL.TX2_241.Ref` (evidence/integrate-20261111/NNH_dependency_inputs/RSL_TX2_241.lean:79; in cone):
`def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) : RS Unit`. This is the row spec of `stage2_owned`. It calls `V.tx2auth` under `Dom064`.
- `structure V2Lib where VErr : Type; debug : VErr → String; Root0 : Bytes → Bytes → Prop; tx2auth : Bytes → Bytes → Bytes → Spec (Except VErr Unit)`
- `def Dom064 (V : V2Lib) (x : Bytes × Bytes × Bytes) : Prop := x.2.1.length = PROOF_BYTES ∧ x.2.2.length = CHECKPOINT_BYTES ∧ x.1.length ≤ STATEMENT_BYTES ∧ V.Root0 x.2.2 x.2.1`

The library bundle (evidence/integrate-20261111/NNH_Libraries.lean, all in cone) is `abbrev L := LIBB_PoolLib.library`, `D := LIB_Instances.D`, `V0 := LIBB_V2Star.library`, `VL := LIB_Instances.VL`, `P := LIB_Instances.P`, `C := LIB_Instances.C`. In evidence/lib-20261111/LIB_Instances.lean these are `VL := LIB_VLib.library`, `P : PreparedNew VL := LIB_Prepared.child`, `C : TX1_345.S1Lib VL := LIB_S1.library` and `D : DeployedIds := LIB_Deployed.deployed`. `NNH_Libraries.tx2Value` is not in the splitB cone, because A2 uses `TX2_241.Ref` directly.

### 2.5 Equivalence theorems (exact statements)

`AspisR1.NOC_Stage1Iff.iff345` (evidence/a1x-20261108/NOC_Stage1Iff.lean, in cone). This is the A1 core.
```lean
theorem iff345 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : _root_.AdapterRw.solana_pubkey.Pubkey)
 (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8) :
 _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (NOC_HostCtx.sdk c) program xs data = .ok (.Ok saved) ↔
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (NOC_Run5bCtx.envOf c) =
  .ok (bytes saved.deref)
```
The forward direction is `NOC_Stage1Forward.ok345` and the converse is `NOC_Stage1Conv.conv`; both are in cone and neither carries an `AspisR1.` prefix. The theorem covers Ok results only. It does not show that a rejected input gives the same error, or the same Err-versus-fail/div outcome, on both sides. The Err transport is the weaker `NNH_ExactRemainingTypes.tx1Err` shape (`∃ pe, … = .ok (.Err pe)`).

`AspisR1.NOQ_FinalCombined.field` (evidence/a1c-20261109/NOQ_FinalCombined.lean, in cone):
```lean
def field {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 RSL.TAS.NND_A1 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C :=
 NOQ_A1Assembly.field_of L0 copy std (fun c => AspisR1.NOC_Stage1Iff.iff345 c)
```

`AspisR1.NOF_Tx2Op11.tx2Op11` (evidence/a2y-20261108/NOF_Tx2Op11.lean, in cone) has the statement `theorem tx2Op11 : NNH_ExactRemainingTypes.tx2Op11`. The proposition comes from evidence/integrate-20261111/NNH_ExactRemainingTypes.lean:11:
```lean
def tx2Op11 : Prop :=
 ∀ (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation),
 NJC_FilledClause.reserved reserve=env.reservation →
 ∀ pub proof ck : Slice U8,
 RSL.TX2_241.Dom064 V0 (bytes pub,bytes proof,bytes ck) →
 LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ()) →
 (NNH_CorrectConfiguration.sdk missing env err reserve).op11
  (SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk missing env err reserve))
  pub proof ck () none=.ok (.Ok ())
```
The direction is "library accepts ⇒ installed op11 accepts", under `Dom064`.

`AspisR1.NOF_A2FieldCorrected.field` (evidence/a2y-20261108/NOF_A2FieldCorrected.lean, in cone):
```lean
def field {W Tx : Type} (L0 : _) (copy : _) (std : _) :
 RSL.TAS.NND_A2 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0
```
The interface comes from evidence/top-assembly-20261107/TAS_Interfaces.lean:
```lean
structure NND_A1 where
  stage1 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX1_345.Ref VL P C a env o → o.exit = .ret r → S.ModelRet1 c a r
structure NND_A2 where
  stage2 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX2_241.Ref L D V0 a env o → o.exit = .ret r → S.ModelRet2 c a r
```
At `S_host`, `ModelRet1` and `ModelRet2` come from `NNE_AcceptanceSig.physical` (evidence/integrate-20261111/NNH_dependency_inputs/NNE_AcceptanceSig.lean:42). `ModelRet1` gives reference Ok ⇒ native Ok with the same bytes, and reference Err ⇒ ∃ native Err. `ModelRet2` gives reference `.ok ()` ⇒ native `Ok ()` only. For privacy this means TX2 is proved in one direction only: the reference accepting implies the native verifier accepts.

## 3. (b) Statement and public-input encoding and validation

`AspisR1.NNH_S1HostCodec.validate` (evidence/integrate-20261111/NNH_S1HostCodec.lean, in cone). It is a hand-written literal fill of the missing `op21` slot, installed by `install (ops : Ops) : Ops := {ops with op21 := validate, op24 := encode}`.
```lean
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev FormatError := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
def validate (st : Statement) : Result (core.result.Result Unit FormatError) :=
 match NMT_345.validateCall (NNH_S1DecodeOk.carrier st) with
 | .ok (.Ok u) => .ok (.Ok u)
 | .ok (.Err _) => .div
 | .fail e => .fail e
 | .div => .div
```
It maps a native validator Err to `.div`. The source says "The weak Err interface permits divergence on rejected values; no error payload is read". If Stream B's transcript covers visible errors, this slot does not model the rejection payload.

`NNH_S1DecodeOk.carrier` (evidence/integrate-20261111/NNH_S1DecodeOk.lean, in cone, hand-written carrier map):
```lean
def carrier (st : AspisS6CurrentCodecInstallation.Statement) : NMT_345.Statement :=
 NMT_345Dec.fromT8 (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)
```
`NNH_S1DecodeOk.source` (in cone) links the library decoder `C.decodeStatement (LIB_Carriers.bytes publicData) = some st` to the native `AspisS6CurrentCodecInstallation.decode publicData = .ok (.Ok native)` with `carrier native = st`.

The semantic-public map is the field `RSL.TX1_345.S1Lib.semanticPublic : Statement → V.Public` (RSL_TX1_345.lean `structure S1Lib`, in cone). Its other fields are `decodeStatement`, `decodeReachesAlloc`, `validateStatement` and `encodeCandidate`. At `NNH_Libraries.C = LIB_S1.library` it is fixed by `LIB_S1.semantic : library.semanticPublic s = AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s)`. The function is `AspisR1.NJB_SemanticPublic.value : PoolV1PairForestTerminalStatementV1 → r0.Public` (evidence/terminal-20261107/NJB_SemanticPublic.lean, in cone, hand-written constructor law, with `.PrivateTransfer common public1 => .Transfer public1 common.lane_transition` and `.Withdrawal common public1 => .Withdrawal public1 common.lane_transition`).

`NOC_Stage1Forward.publicBinding` (evidence/a1x-20261108/NOC_Stage1Forward.lean:90, in cone):
```lean
theorem publicBinding (st : NNH_S1HostCodec.Statement) :
 ∃ sp, aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public st = ok sp ∧
  AspisS6CurrentVerifierCarrier.toPublic sp =
  AspisR1CurrentCaller.FirstComposition.toCurrentPublic (C.semanticPublic (NNH_S1DecodeOk.carrier st))
```
It states that the emitted `semantic_public`, carried to the current caller, equals the library's `C.semanticPublic` of the same decoded statement.

`LIB_VPublicDomain.publicDom` and `LIB_VPublicDomain.publicDigestDom` (evidence/lib-20261111/LIB_VPublicDomain.lean, both in cone, hand-written):
```lean
def publicDigestDom (p : Public) : Prop :=
 NKR_DigestChildren.Domain (NKR_TermPublic.value (FIq_Carriers.toPublic p))
def publicAssetDom (p : Public) : Prop :=
 (NKR_TermPublic.value (FIq_Carriers.toPublic p)).asset_id.val<2147483647
def publicDom (p : Public) : Prop := publicDigestDom p ∧ publicAssetDom p
```
Here `Public := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public` (LIB_VCarriers.lean:8). `LIB_VPublicDomain.hd_omits_asset` records that the digest half does not imply the asset half.

`AspisR1.NOM_TerminalDomain.reached` (evidence/a1b-20261109/NOM_TerminalDomain.lean:58):
```lean
theorem reached (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ()))
 (a : LIB_VTerminal.Args) (same : a.1 = NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st))
 (r : RSL.B32) (env : RSL.Env) (t : Transcript)
 (returned : LIB_VLib.publicTranscriptValue (a.1,r) env = .ok t) :
 LIB_VTerminal.Domain a
```
**`reached` is not in the splitB cone.** The cone contains its components, all `AspisR1.NOM_TerminalDomain.*`: `validate_native`, `validated_digest`, `domain`, `asset` and `terminal`. `validated_digest` has the signature `(st) (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) : LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st))`.

## 4. (c) Transcript and challenge derivation as the verifier computes it

The verify prefix at the installed op9 slot is given by `AspisR1.NOC_Op9Slot.slot` (in cone):
```lean
theorem slot {W Tx : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 Unit)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) :
 (DrvC_Installation.currentInstalled (configuration c)).op9 D pub bytes () none =
 S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls c.fixed.reservation)
   (IDa_Deployed.boundaries c.fixed.reservation)) D pub bytes () := rfl
```
`AspisR1.NOC_Op9Slot.prefix_finish` (in cone) evaluates `AspisR1PublicPreparation.VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children NOC_FinishSource.Bi) (LIB_VCode.digest env) pub bytes () none` to `.ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem))` from the same returned library value. `AspisR1.NOC_Op9.op9` (in cone) then states that the installed `op9` returns `.ok (.Ok (NNV_PreparedInputs.sem sem))`.

The following three models are boundary-parameterised. None has an Aeneas header or a PCXD record. All three are in cone.

`AspisR1PublicPreparation.VerifyPrefix.verify` (docs/research/100bit-spend-path-20261013/lean/bridge-verify-prefix-fe80-20261017/ExtractedVerifyPrefixModel.lean:15):
```lean
abbrev VerifyPrefix.Finish := {H : Type} → aspis_core.Digest32 H →
  pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
def VerifyPrefix.verify (F : VerifyPrefix.Finish)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
```
It parses (`PrefixAdapter.parseAccepted`), runs the public transcript and begin, then the finish `F`.

`AspisR1PublicPreparation.RoundModel.rounds` (docs/research/100bit-spend-path-20261013/lean/ExtractedSemanticRoundsModel.lean:100):
```lean
def RoundModel.rounds (B : RoundModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
```
This is the 10-round alpha producer over transcript rows 15 to 24. The record is `structure RoundModel.Boundaries where decode … ; boundary … ; value …`.

`AspisR1PublicPreparation.FinishModel.finish` (docs/research/100bit-spend-path-20261013/lean/bridge-finish-a555-20261017/ExtractedVerifyFinishModel.lean:225):
```lean
def FinishModel.finish (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
  (challenges : r1_wire.Challenges)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
```
`FinishModel.Boundaries` has the fields `fromFn`, `mask`, `add`, `mul`, `terminal`, `circle`, `unwrapRoot` and `claims`. The installed instance is `AspisR1.NOC_FinishSource.Bi := AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install (NP6_StdModel.calls (.Ok ())) (IDa_Deployed.boundaries (.Ok ())))`, which is in cone.

The next four producers are Aeneas emissions of crate `aspis_r1_public_preparation` (a probe crate). They are in cone and have no PCXD definition record. They were read from docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean. L187_SOURCE_MANIFEST lists `AspisR1PublicPreparation.Funs` under "recovered_but_committed_copy_at_module_path_differs_or_absent", so the compiled gate copy may differ textually from this file.
- `AspisR1PublicPreparation.r1_semantic.public_transcript {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (c1_root : Array Std.U8 32#usize) : Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)` (line 2749). This absorbs the public input into the transcript.
- `AspisR1PublicPreparation.r1_wire.begin {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) : Result ((core.result.Result r1_wire.Challenges r1_wire.Error) × (r1_wire.SemanticTranscript H))` (line 2119). This produces the begin challenges lambda, chi, theta, mu, eta and zc.
- `AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) : Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × (r1_wire.SemanticTranscript H))` (line 2091). This is one squeeze. It calls `sampler.qm31_sample` at line 2108.
- `AspisR1PublicPreparation.sampler.qm31_sample (block : Array Std.U8 32#usize) : Result aspis_core.field.QM31` (line 2007). This is **the verifier's own copy of the sampler, and a different constant from `AspisR1Qm31SamplerIndex.sampler.qm31_sample`.**

The begin, round and alpha canonicality producers (theorems, in cone):
- `AspisR1.FJn_BeginCanonical.value` (/Users/dominic/ZK/lean/FJn_BeginCanonical.lean): `theorem value {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) (run : r1_wire.begin D pre before=ok (.Ok c,after)) : FIp_SemanticValues.Canon c.lambda ∧ FIp_SemanticValues.Canon c.chi ∧ FIp_SemanticValues.Canon c.theta ∧ FIp_SemanticValues.Canon c.mu ∧ FIp_SemanticValues.Canon c.eta ∧ ∀ x∈c.zc.val,FIp_SemanticValues.Canon x`. There is no separately named "eta producer". Eta is the `c.eta` conjunct of this theorem.
- `AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical` (docs/research/100bit-spend-path-20261013/lean/SemanticRoundAlphaSelectedCanonical.lean:40): `theorem verifier_round_alpha_canonical {H : Type} (B : AspisR1PublicPreparation.RoundModel.Boundaries) (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (pre : AspisR1PublicPreparation.r1_wire.Prefix) (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) (running : PublicQM) (alpha : Array PublicQM 10#usize) (h : AspisR1PublicPreparation.RoundModel.rounds B D pre self = ok (.Ok (running, alpha, after))) : ∀ i : Fin 10, SelectedCanonical (ToSelected (alpha.val[i.val]'(…)))`.

The NNV transcript and prefix links (theorems, evidence/a1-20261108, in cone):
- `AspisR1.NNV_SemanticTranscript.source (a : LIB_VCarriers.Public × RSL.B32) (env : RSL.Env) : (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 = r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2)`
- `AspisR1.NNV_SemanticTranscript.returned (a) (env) (t : LIB_VCarriers.Transcript) (called : LIB_VLib.publicTranscriptValue a env = .ok t) : r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2) = .ok (.Ok t)`
- `AspisR1.NNV_SemanticPrefix.returned (pub : VL.Public) (bytes : Slice U8) (env : RSL.Env) (sem : RSL.Verified VL) (called : NNH_ObservedReturns.value ⟨pub,LIB_Carriers.bytes bytes⟩ env = .ok sem) : ∃ p : NNV_ObservedCut.Packet ⟨pub,LIB_Carriers.bytes bytes⟩ env sem, PrefixAdapter.parseAccepted bytes = .ok (.Ok (LIB_VCarriers.prefixRaw p.prefix_)) ∧ r1_semantic.public_transcript (LIB_VCode.digest env) pub () (LIB_Env.nativeKey (VL.c1Root p.prefix_)) = .ok (.Ok p.initial) ∧ r1_wire.begin (LIB_VCode.digest env) (LIB_VCarriers.prefixRaw p.prefix_) p.initial = .ok (.Ok (LIB_VCarriers.challengesRaw p.challenges),p.before)`
- The NNV_PreparedInputs carrier maps, all in cone: `abbrev sem (s : RSL.Verified LIB_VLib.library) := S1SemanticCarrier.currentSem (LIBC_PreparedCarriers.verified LIB_Prepared.types s)`, `def view (v : LIB_VCarriers.View) : verifier.View` and `abbrev scratch (g : LIB_VCarriers.E29)`.
- The prepare front: `AspisR1.NOC_PrepareFront.source` (in cone) states `verifier.candidate.prepare (cur c) (NNV_PreparedAtHost.digest c) (FirstComposition.toCurrentPublic pub) proof () none (NNV_PreparedInputs.scratch g) = .ok (.Ok (InstalledPreparation.currentPrepared prep), NNV_PreparedInputs.scratch g')` from `NNH_Tx1Returns.preparedValue … = .ok (prep,g')`, given `proof.val.length = 57607`. Here `cur c := DrvC_Installation.currentInstalled (NOC_Run5bCtx.configuration c)`.

The sampler extraction constants are all Aeneas emissions of probe crates, all PROBE_OR_CUT_CRATE, and all OPEN with NO_FRESH_EMISSION in PCXD. All are in both the soundness cone and the privacy cone; they appear in evidence/model-intersection-20261110/SHARED_PROJECT_CONSTANTS.txt. "AspisR1Post25Sampler.sampler" and the similar names in the brief are namespaces, not constants. The constants are:
- `AspisR1Qm31SamplerIndex.sampler.qm31_sample (block : Array Std.U8 32#usize) : Result field.QM31` (crate `aspis_r1_qm31_index_sampler_extract`; docs/research/100bit-spend-path-20261013/lean/extracted-qm31-index-sampler-20261016/AspisR1Qm31SamplerIndex/Funs.lean:155), with `sampler.qm31_digits`, `qm31_digits_loop0/1`, `qm31_div_pass` and `qm31_div_pass_loop`. The field is `AspisR1Qm31SamplerIndex.field.{M31,CM31,QM31,P}`.
- `AspisR1Post25Sampler.sampler.ordinary_sample (block : Array Std.U8 32#usize) : Result field.WideExact` (crate `r1_post25_sampler_extraction`; docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:210), with `sampler.decode8`, `low_base_p_digits` (and loops 0/1) and `qm31_div_pass` (and loop). The field is `AspisR1Post25Sampler.field.{M31,CM31,QM31,WideExact,P,canonical_qm31}`.
- `AspisR1GammaCaller.sampler.gamma_sample (ops : GammaHelpers) (block : Array Std.U8 32#usize) : Result field.WideExact` (crate `aspis_r1_stage2_adopted_caller`; gate module GammaCallerExplicitHelpers, docs/research/v8-r0-zk-20261009/lean/GammaCallerExplicitHelpers.lean:30, byte-identical to evidence/prov-p2d-20261109/inputs/gate_GammaCallerExplicitHelpers.lean). It is parametric in the hand-written `structure GammaHelpers where low … ; add … ; decode …`. The field is `AspisR1GammaCaller.field.{M31,CM31,QM31,WideExact}` (module AspisR1GammaCaller.Types).

The bridge from the verifier's sampler to the shared sampler is `AspisR1PublicPreparation.SamplerTransport.sample_eq` (gate module RPz7_ExtractedDigest32SamplerTransport, in cone; the copy read is docs/research/100bit-spend-path-20261013/lean-candidates/prepared-post25-query-rho-caller-20261020/dependencies/ExtractedDigest32SamplerTransport.lean:45):
```lean
theorem sample_eq (block : Array U8 32#usize) :
    (do let q ← sampler.qm31_sample block; ok (toOld q)) =
      AspisR1Qm31SamplerIndex.sampler.qm31_sample block
```
`div_pass_eq` and `digits_eq` are in cone too. **The `AspisR1PublicPreparation` namespace is not in the privacy cone at all (0 shared constants).** So privacy today shares the sampler function but not the verifier's transcript (public_transcript, begin, semantic_validated) that calls it. I did not trace the corresponding Post25 and Gamma bridges. The cone contains `AspisR1Post25SamplerOrdinaryCallbackV2`, `AspisR1Post25SamplerPreparedCarrier`, `NKU_Gamma*` and `AspisR1GammaCaller.DigitsModel.*`.

## 5. Recommendation to Stream B

Stream A suggests the following, as information for Stream B's design choice rather than an instruction.

1. For the verifier the privacy theorem refers to, use `AdapterRw.r1_pool_adapter.owned.stage1_owned` and `stage2_owned` at `NNH_CorrectConfiguration.sdk (AspisR1.NOC_HostSeed.m0 r) env err r`. That equals `AspisR1.NOC_HostCtx.sdk c` by `sdk_at_slot`. For the transcript, use `AspisR1PublicPreparation.r1_semantic.public_transcript`, `r1_wire.begin`, `r1_wire.SemanticTranscript.semantic_validated` and `sampler.qm31_sample`, linked to the already shared `AspisR1Qm31SamplerIndex.sampler.qm31_sample` by `SamplerTransport.sample_eq`. Privacy would then rest on the same constants as soundness, and would inherit exactly the same provenance status: OPEN at Stream C.
2. Use the RSL and LIB constants (`RSL.TX1_345.Ref`, `RSL.TX2_241.Ref`, `NNH_Libraries.*`, `NNH_ReturnsBundle.tx1Value`) only through the equivalence theorems, and only in the direction those theorems prove. TX1 Ok is an iff; TX1 Err is only "∃ native Err"; TX2 is only reference-Ok ⇒ native-Ok. The op21 validator maps native Err to `.div`. Any privacy claim about rejection paths or visible errors needs a stronger transport than the one that exists now.
3. The soundness and privacy cones do not yet meet on any of these constants. As of 2026-11-10 they share only the field, Poseidon, the spend relation and the sampler extraction (INTERSECTION.md). Adopting these constants is new work for Stream B, and it does not close any existing gap.

## 6. Names not located or not as briefed

- `NOC_HostSeed.lean` does not exist as a file. `AspisR1.NOC_HostSeed` is defined inside NOC_Run5bHost.lean.
- `AspisR1.NOM_TerminalDomain.reached` exists but is not in the splitB cone. Its components are.
- `NNH_Libraries.C.semanticPublic` is a structure projection (`RSL.TX1_345.S1Lib.semanticPublic`) applied to `LIB_S1.library`. It is not a standalone constant.
- `AspisR1Post25Sampler.sampler`, `AspisR1Qm31SamplerIndex.sampler`, `AspisR1GammaCaller.sampler` and `AspisR1GammaCaller.field` are namespaces. The constants are listed in section 4.
- The textual identity of the committed AspisR1PublicPreparation/Funs.lean with the compiled gate copy was not established (see the L187 manifest note in section 4).

target not yet established
