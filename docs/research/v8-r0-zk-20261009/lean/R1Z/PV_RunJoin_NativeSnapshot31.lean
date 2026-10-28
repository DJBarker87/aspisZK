import R1Z.PV_RunJoin_SnapshotAgreement31
import R1Z.PV_RunJoin_NativeSelectedInputs
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeSnapshot31
open Aeneas Aeneas.Std Result
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩

def live (base : ProverRwFull.ExternalTypes) (p : PV_RunJoin_NominalPublicData.TargetPublic base) :
    PV_RunJoin_NominalLeafData.TargetSnapshot := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact match p with
    | .Transfer _ transition => transition.live_snapshot
    | .Withdrawal _ transition => transition.live_snapshot

theorem from_input (base : ProverRwFull.ExternalTypes) (i : PV_Src_NativeInput.Input) :
    live base (PV_RunJoin_NominalPublicData.fromInput base i) =
      PV_RunJoin_NominalLeafData.snapshot i.compiled.public_statement.live_snapshot := by
  cases i with
  | mk request witness change lane snapshot compiled => cases request <;> rfl
#print axioms from_input

local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped

theorem actual (base : ProverRwFull.ExternalTypes) (i : PV_Src_NativeInput.Input)
    (h : PV_Src_NativeInput.run i = ok (.Ok i.compiled)) :
    live base (PV_RunJoin_NominalPublicData.fromInput base i) =
      PV_RunJoin_NominalLeafData.snapshot i.snapshot := by
  rw [from_input,PV_RunJoin_UniversalRecords22.snapshot i h]
#print axioms actual

theorem caller {N C : Type} (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C → @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C)
    (h : PV_Src_NativeInput.run i = ok (.Ok i.compiled)) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    live base ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i).pub s) =
      PV_RunJoin_NominalLeafData.snapshot i.snapshot := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact actual base i h
#print axioms caller
end R1Z.PV_RunJoin_NativeSnapshot31
