import re,sys
def boundex(path):
    t=open(path).read()
    i=t.index('theorem bound_exists')
    body=t[i:]
    # lines of the exact block
    m=re.search(r"  exact ⟨ops, \{\n(.*?)\n    \}, ⟨(.*?)⟩⟩\nend ",body,re.S)
    return m.group(1),m.group(2)
HDR='''import Aeneas
import NNH_CorrectConfiguration
import NNH_HostSeed
import NNH_HostCtx
import NNH_Tx2SourceConfiguration
import PRVEq_%s_o1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
'''
# ---------- stage1
fields,tup=boundex('PRVEq_AdapterStage1_o1.lean')
s=HDR%'AdapterStage1'
s=s.replace('PCVO','PCVO')
s+='''namespace PCVO_S1
open AdapterRw AdapterRw.PCVK_S1

/-- The externals read off the Ops: every field is the gate counterpart of the Ops (organisation, see PCVO_HANDOFF.md). -/
def xOf (ops : AdapterRw.Ops) : Ext := {
%s
  }

theorem bound (ops : AdapterRw.Ops) : Bound ops (xOf ops) := ⟨%s⟩

theorem generic_stage1_owned (ops : AdapterRw.Ops) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf ops) = AdapterRw.r1_pool_adapter.owned.stage1_owned ops :=
  PRVEq.AdapterStage1_k1.r1_pool_adapter_owned_stage1_owned_eq (bound ops)

theorem generic_data (ops : AdapterRw.Ops) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.OwnedAccount.data (xOf ops) = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops :=
  PRVEq.AdapterStage1_k1.data_eq (bound ops)

/-- The deployed Adapter Ops of the credited host context: NNH_CorrectConfiguration.sdk (every `missing`). -/
theorem deployed_stage1_owned (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_CorrectConfiguration.sdk missing env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err r) :=
  generic_stage1_owned _

theorem deployed_stage1_owned_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) :=
  generic_stage1_owned _

theorem deployed_stage1_owned_src (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_Tx2SourceConfiguration.sdk missing env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_Tx2SourceConfiguration.sdk missing env err r) :=
  generic_stage1_owned _

/-- The Adapter model of the credited host context (NNH_HostCtx.model1): fresh frozen stage1_owned at xOf = model1 c. -/
theorem host_model1 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (AspisR1.NNH_HostCtx.sdk c)) = AspisR1.NNH_HostCtx.model1 c :=
  generic_stage1_owned _

#print axioms bound
#print axioms generic_stage1_owned
#print axioms deployed_stage1_owned
#print axioms deployed_stage1_owned_m0
#print axioms deployed_stage1_owned_src
#print axioms host_model1
end PCVO_S1
'''%(fields,tup)
open('PRVEq_AdapterStage1Deployed_o1.lean','w').write(s)

# ---------- stage2
fields,tup=boundex('PRVEq_AdapterStage2_o1.lean')
fields=fields.replace('Hash := Unit','Hash := Array Std.U8 32#usize')
a='solana_sha256_hasher_hashv := fun _ => Result.fail Error.panic'
b='solana_hash_Hash_to_bytes := fun _ => Result.fail Error.panic'
assert a in fields and b in fields
fields=fields.replace(a,'solana_sha256_hasher_hashv := hashv').replace(b,'solana_hash_Hash_to_bytes := fun h => ok h')
parts=[p.strip() for p in tup.split(',')]
# fun _ => rfl contains no comma split problem? check count
parts=re.split(r',\s*(?![^()]*\))',tup)
parts=[p.strip() for p in parts]
assert len(parts)==40,len(parts)
parts[38]="h42"; parts[39]="h43'"
tup2=', '.join(parts)
s=HDR%'AdapterStage2'
s+='''namespace PCVO_S2
open AdapterRw AdapterRw.PCVK_S2

theorem bind_ok_id {α : Type} (x : Result α) : (x >>= fun h => ok h) = x := by cases x <;> rfl

/-- The externals read off the Ops, with the hash library fields instantiated by `hashv` (Hash := Array U8 32, to_bytes := ok). -/
def xOf (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) : Ext := {
%s
  }

theorem bound (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) : Bound ops (xOf ops hashv) := by
  have h43' : ops.op43 = AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest (xOf ops hashv) := by
    rw [h43]; funext s parts
    unfold AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest xOf
    exact (bind_ok_id (hashv parts)).symm
  exact ⟨%s⟩

theorem generic_stage2_owned (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf ops hashv) = AdapterRw.r1_pool_adapter.owned.stage2_owned ops :=
  PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_stage2_owned_eq (bound ops hashv h42 h43)

theorem generic_validate_asq8 (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.validate_asq8 (xOf ops hashv) = AdapterRw.r1_pool_adapter.owned.validate_asq8 ops :=
  PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_validate_asq8_eq (bound ops hashv h42 h43)

theorem deployed_stage2_owned (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (NNH_CorrectConfiguration.sdk missing env err r) (LIB_Env.hashv env)) =
      AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk missing env err r) :=
  generic_stage2_owned _ _ rfl rfl

theorem deployed_stage2_owned_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) (LIB_Env.hashv env)) =
      AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) :=
  generic_stage2_owned _ _ rfl rfl

theorem host_model2 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (AspisR1.NNH_HostCtx.sdk c) (LIB_Env.hashv (AspisR1.NNH_HostCtx.envOf c))) =
      AspisR1.NNH_HostCtx.model2 c :=
  generic_stage2_owned _ _ rfl rfl

#print axioms bound
#print axioms generic_stage2_owned
#print axioms generic_validate_asq8
#print axioms deployed_stage2_owned
#print axioms deployed_stage2_owned_m0
#print axioms host_model2
end PCVO_S2
'''%(fields,tup2)
open('PRVEq_AdapterStage2Deployed_o1.lean','w').write(s)

# ---------- caller
fields,tup=boundex('PRVEq_CallerPrepTx1_o1.lean')
parts=[p.strip() for p in re.split(r',\s*(?![^()]*\))',tup)]
n=len(parts); assert n==23,n
parts[17:23]=['c2','c12','c13','c14','c15','c21']
tup2=', '.join(parts)
p3m=open('../prov-p3m-20261110/PRVEq_Tx2Deployed_m1.lean').read()
i=p3m.index('-- Usize literal arithmetic'); j=p3m.index('theorem v_OFF_Y1')
lits=p3m[i:j]
k=p3m.index('theorem v_OFF_Y1'); l=p3m.index('#print axioms v_OFF_ROUND1')
rest=p3m[k:l]
s=HDR%'CallerPrepTx1'
s=s.replace('import NNH_HostSeed','import NNH_HostSeed\nimport NJG_CallerInstall')
s+='''namespace PCVO_C
open AspisR1CurrentCaller.PCVK_C

'''+lits+rest+'''
/-- The externals read off the Ops; the six constant fields are the fresh definitions. -/
def xOf (ops : AspisR1CurrentCaller.Ops) : Ext := {
%s
  }

theorem bound (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) : Bound ops (xOf ops) := by
  have c2 : ops.op2 = AspisR1CurrentCaller.PCVK_C.verifier.Error.Insts.CoreConvertFromCodecError.from := by rw [h2]; rfl
  have c12 : ops.op12 = ok AspisR1CurrentCaller.PCVK_C.compact.OFF_SEMANTIC := by rw [h12]; with_unfolding_all rfl
  have c13 : ops.op13 = AspisR1CurrentCaller.PCVK_C.compact.COMPACT_SEMANTIC := by rw [h13, v_COMPACT_SEMANTIC]
  have c14 : ops.op14 = AspisR1CurrentCaller.PCVK_C.compact.COMPACT_Y1 := by rw [h14, v_COMPACT_Y1]
  have c15 : ops.op15 = AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_SEMANTIC := by
    rw [h15]; unfold AspisR1CurrentCaller.PCVK_C.compact.LOGICAL_SEMANTIC; rw [v_SEMANTIC_BYTES]
  have c21 : ops.op21 = AspisR1CurrentCaller.PCVK_C.compact.OFF_ROUND0 := by rw [h21, v_OFF_ROUND0]
  exact ⟨%s⟩

theorem generic_prepare (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf ops) H = @AspisR1CurrentCaller.verifier.candidate.prepare ops H :=
  PRVEq.CallerPrepTx1_k1.verifier_candidate_prepare_eq (bound ops h2 h12 h13 h14 h15 h21) H

theorem generic_tx1 (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 (xOf ops) H = @AspisR1CurrentCaller.verifier.candidate.tx1 ops H :=
  PRVEq.CallerPrepTx1_k1.verifier_candidate_tx1_eq (bound ops h2 h12 h13 h14 h15 h21) H

section
variable (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
  (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

/-- The deployed CurrentCompact Ops of the credited host context. -/
abbrev cur := DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration missing env err r)

theorem deployed_prepare (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf (cur missing env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur missing env err r) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem deployed_tx1 (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 (xOf (cur missing env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (cur missing env err r) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H
end

theorem deployed_prepare_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf (cur NNH_HostSeed.m0 env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur NNH_HostSeed.m0 env err r) H :=
  deployed_prepare _ _ _ _ H

theorem deployed_tx1_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 (xOf (cur NNH_HostSeed.m0 env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (cur NNH_HostSeed.m0 env err r) H :=
  deployed_tx1 _ _ _ _ H

/-- The packet Ops of the credited emitted-tx1 chain (NHL_DriverModel): every base/expected/reserved. -/
theorem packet_prepare (base expected : AspisR1CurrentCaller.Ops) (reserved : Bool) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf (NHL_DriverModel.preparedOps base expected reserved)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (NHL_DriverModel.preparedOps base expected reserved) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem packet_tx1 (base expected : AspisR1CurrentCaller.Ops) (reserved : Bool) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 (xOf (NHL_DriverModel.txOps base expected reserved)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (NHL_DriverModel.txOps base expected reserved) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H

/-- Composition with the existing NJG_CallerInstall.tx1 (emitted tx1 = gate tx1 at the packet Ops):
the PCVK fresh frozen tx1 at xOf equals NHW_EmittedTx1.tx1 at the installed packet Ops. -/
theorem njg_tx1 (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice Std.U8) (k : Std.Usize) (hash : H) :
    NHW_EmittedTx1.tx1
      (NHL_Packets.installed
        (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
          (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved)
      (NHW_EmittedPrepare.prepare
        (NHL_Packets.installed
          (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
            (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved))
      D pubdata publicBytes proof k hash none =
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1
      (xOf (NHL_DriverModel.txOps
        (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
          (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))
        (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std) reserved)) H
      D pubdata publicBytes proof k hash none := by
  rw [packet_tx1]
  exact NJG_CallerInstall.tx1 base reserved seed std D pubdata publicBytes proof k hash

theorem njg_prepare (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H) (g : NHL_PrepareStages.Scratch) :
    NHL_EmittedPrepare.prepare
      (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
      D pubdata proof hash none g =
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare
      (xOf (NHL_PrepareModel.children
        (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
        (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))) H
      D pubdata proof hash none g := by
  have := packet_prepare (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std))
    (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std) reserved H
  unfold NHL_DriverModel.preparedOps at this
  rw [this]
  exact NJG_CallerInstall.prepare base reserved seed std D pubdata proof hash g

#print axioms bound
#print axioms generic_prepare
#print axioms generic_tx1
#print axioms deployed_prepare
#print axioms deployed_tx1
#print axioms deployed_prepare_m0
#print axioms deployed_tx1_m0
#print axioms packet_prepare
#print axioms packet_tx1
#print axioms njg_tx1
#print axioms njg_prepare
end PCVO_C
'''%(fields,tup2)
open('PRVEq_CallerPrepTx1Deployed_o1.lean','w').write(s)
