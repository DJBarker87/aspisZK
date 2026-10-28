import R1Z.PV_RunJoin_SelectedCoordinates32
import R1Z.PV_Src_NativeIdentification
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestPremises32
open Aeneas Aeneas.Std Result PV_RunJoin_HonestIdentification26
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- All five native-source conditions are derived on the same honest family;
none is an additional hypothesis and the original record type is unchanged. -/
theorem premises : PV_Src_NativeIdentification.PV_Src_Premises (K := K)
    (inputs (K := K)) PV_Src_Transport.transport where
  compile_call := success
  words := fun i r hr => PV_RunJoin_UniversalRecords22.words (inputs i) i.property.2.2.1 r hr
  publicCorr := fun i r hr => PV_RunJoin_UniversalRecords22.publicCorr (inputs i)
    (success i) i.property.2.2.2 r hr
  admission := by
    intro i r hr
    have he := PV_RunJoin_UniversalRecords22.returned (inputs i) r hr
    rw [he]
    exact admitted i
  row_call := fun _ => rfl
#print axioms premises

/-- The constructor's actual returned record is the same record used by the
universal target; no new cached payload or mathematical witness is selected. -/
theorem record_eq (i : Honest (K := K)) :
    PV_Src_NativeIdentification.records (premises (K := K)) i =
      PV_RunJoin_UniversalBuild22.records (inputs i) :=
  PV_RunJoin_UniversalRecords22.returned (inputs i) _
    (PV_Src_NativeIdentification.records_success premises i)
#print axioms record_eq

theorem target_eq (i : Honest (K := K)) :
    PV_Src_NativeIdentification.toInstance premises i = target i := by
  apply Subtype.ext
  change (_,BuilderRecordCanonical.witness
    (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_Src_NativeIdentification.records premises i).w)) = _
  rw [record_eq]
  rfl
#print axioms target_eq

theorem identification : BuilderSource.SourceIdentification
    (source_honest (K := K)) target := by
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (PV_Src_NativeIdentification.public_eq premises i).trans
      (congrArg (fun w : BuilderCanonical.Instance (K := K) => BuilderSource.prover.public w)
        (target_eq i))
  · intro i
    exact (PV_Src_NativeIdentification.build_eq premises i).trans
      (congrArg (fun w : BuilderCanonical.Instance (K := K) => BuilderSource.prover.build w)
        (target_eq i))
  · exact PV_Src_NativeIdentification.transport_eq premises
#print axioms identification
end R1Z.PV_RunJoin_HonestPremises32
