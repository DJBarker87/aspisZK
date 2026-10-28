import R1Z.PV_RunJoin_SelectedCoordinates32
import R1Z.PV_RunJoin_NativeSnapshot31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSnapshotAgreement32
open Aeneas Aeneas.Std Result PV_RunJoin_HonestIdentification26
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem snapshots (a b : Honest (K := K))
    (same : source_honest.public a = source_honest.public b)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain) :
    a.val.snapshot=b.val.snapshot := by
  have ha := PV_RunJoin_UniversalPublic22.projection (K := K) (inputs (K := K)) PV_Src_Transport.transport a
  have hb := PV_RunJoin_UniversalPublic22.projection (K := K) (inputs (K := K)) PV_Src_Transport.transport b
  exact PV_RunJoin_SnapshotAgreement31.whole (K := K) a.val b.val (success a) (success b)
    a.property.2.2.2 b.property.2.2.2 (ha.symm.trans (same.trans hb)) pool domain
#print axioms snapshots

local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩

theorem caller_live {N C : Type} (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : Honest (K := K)) (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NativeSnapshot31.live base
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).pub s) =
      PV_RunJoin_NominalLeafData.snapshot i.val.snapshot := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NativeSnapshot31.caller base ops hash i.val s (success i)
#print axioms caller_live

/-- Complete initial native snapshot agreement at the actual emitted-body
inputs; context-byte equality remains explicit, root/sequence are derived. -/
theorem callers_agree {N C : Type} (base : ProverRwFull.ExternalTypes)
    (opsA opsB : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hashA hashB : Slice (Slice U8) → Result (Array U8 32#usize))
    (a b : Honest (K := K))
    (s t : PV_RunJoin_NativeSelectedInputs.SourceState base N C)
    (same : source_honest.public a = source_honest.public b)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_NativeSnapshot31.live base
      ((PV_RunJoin_NativeSelectedInputs.inputs base opsA hashA a.val).pub s) =
    PV_RunJoin_NativeSnapshot31.live base
      ((PV_RunJoin_NativeSelectedInputs.inputs base opsB hashB b.val).pub t) := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact (caller_live base opsA hashA a s).trans
    ((congrArg PV_RunJoin_NominalLeafData.snapshot (snapshots a b same pool domain)).trans
      (caller_live base opsB hashB b t).symm)
#print axioms callers_agree
end R1Z.PV_RunJoin_NativeSnapshotAgreement32
