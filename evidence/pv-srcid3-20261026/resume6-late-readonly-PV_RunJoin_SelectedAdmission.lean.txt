import R1Z.PV_RunJoin_SourceSelectionContract
import R1Z.PV_Src_NativePremises
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedAdmission
open Aeneas Aeneas.Std Result R0P R0Z.ZkStatement R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_Forest_PrimitiveArguments PV_Src_NativeInput
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective AspisCircleGroupOrder.P
variable [ExternalLinear] [Records]
variable {CommitHandle : Type}
variable (d : PV_RunJoin_SourceSelectionContract.Data (CommitHandle := CommitHandle))
    (x : Statement K CommitHandle)
local notation "selected" => fun w => PV_RunJoin_SourceSelectionContract.selectedRecord d x w
local notation "transport" => PV_RunJoin_SourceSelectionContract.endpointHonest.transport

/-- Same selected records and exact original endpoint transport. The four
remaining source fields are explicit; row_call is a theorem, not an input. -/
structure Remainder : Prop where
  compile_call : ∀ w, run (selected w) = ok (.Ok (selected w).compiled)
  words : ∀ w records, newRecords (selected w) = ok records → WitnessOk (wordWitness records.w)
  publicCorr : ∀ w records, newRecords (selected w) = ok records →
    PubCorr (wordPublic records.p)
      (mapPub («K» := K) (PV_Src_Public.canonicalPublic (publicInput (selected w))))
  admission : ∀ w records, newRecords (selected w) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub («K» := K) (PV_Src_Public.canonicalPublic (publicInput (selected w))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))

def toPremises (remaining : Remainder d x) :
    PV_Src_NativeIdentification.PV_Src_Premises («K» := K) selected transport where
  compile_call := remaining.compile_call
  words := remaining.words
  publicCorr := remaining.publicCorr
  admission := remaining.admission
  row_call := PV_RunJoin_SourceSelectionContract.installed_row

#print Remainder
#print axioms toPremises
end R1Z.PV_RunJoin_SelectedAdmission
