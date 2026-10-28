import R1Z.PV_RunJoin_SelectedAdmission
import R1Z.PV_RunJoin_SelectedSourceCore
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedSourceReduction
open Aeneas Aeneas.Std Result R0P R0Z.ZkStatement R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_Forest_PrimitiveArguments PV_Src_NativeInput
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective AspisCircleGroupOrder.P
variable {CommitHandle : Type}

/-- Two source joins remain indispensable: the actual dictionaries must equal
these owned references, and the actual selected record must equal the encoded
canonical record. Neither equality follows from the record's type or name. -/
theorem words_and_public
    (actualExternal : ExternalLinear) (actualRecords : Records)
    (external_eq : actualExternal = PV_Src_FrozenInput.external)
    (records_eq : actualRecords = PV_Src_FrozenInput.records)
    (d : PV_RunJoin_SourceSelectionContract.Data (CommitHandle := CommitHandle))
    (x : Statement K CommitHandle)
    (canonical : PV_RunJoin_SourceSelectionContract.endpointHonest.Instance →
      PV_Src_FrozenInput.Data («K» := K))
    (selected_eq : ∀ w, PV_RunJoin_SourceSelectionContract.selectedRecord d x w =
      PV_Src_FrozenInput.input (canonical w))
    (compile_call : ∀ w,
      @run actualExternal actualRecords (PV_RunJoin_SourceSelectionContract.selectedRecord d x w) =
        ok (.Ok (PV_RunJoin_SourceSelectionContract.selectedRecord d x w).compiled)) :
    (∀ w records,
      @newRecords actualRecords (PV_RunJoin_SourceSelectionContract.selectedRecord d x w) = ok records →
        WitnessOk (wordWitness records.w)) ∧
    (∀ w records,
      @newRecords actualRecords (PV_RunJoin_SourceSelectionContract.selectedRecord d x w) = ok records →
        PubCorr (wordPublic records.p)
          (mapPub («K» := K) (PV_Src_Public.canonicalPublic
            (publicInput (PV_RunJoin_SourceSelectionContract.selectedRecord d x w))))) := by
  exact PV_RunJoin_SelectedSourceCore.words_and_public actualExternal actualRecords external_eq records_eq
    (PV_RunJoin_SourceSelectionContract.selectedRecord d x) canonical selected_eq compile_call

/-- Fill the ORIGINAL admission interface; row_call remains a published source
fact. This is a source reduction conditional on exact installation equalities,
not a new deployed instance and not a new trust item. -/
def remainder
    (actualExternal : ExternalLinear) (actualRecords : Records)
    (external_eq : actualExternal = PV_Src_FrozenInput.external)
    (records_eq : actualRecords = PV_Src_FrozenInput.records)
    (d : PV_RunJoin_SourceSelectionContract.Data (CommitHandle := CommitHandle))
    (x : Statement K CommitHandle)
    (canonical : PV_RunJoin_SourceSelectionContract.endpointHonest.Instance →
      PV_Src_FrozenInput.Data («K» := K))
    (selected_eq : ∀ w, PV_RunJoin_SourceSelectionContract.selectedRecord d x w =
      PV_Src_FrozenInput.input (canonical w))
    (compile_call : ∀ w,
      @run actualExternal actualRecords (PV_RunJoin_SourceSelectionContract.selectedRecord d x w) =
        ok (.Ok (PV_RunJoin_SourceSelectionContract.selectedRecord d x w).compiled))
    (admission : ∀ w records,
      @newRecords actualRecords (PV_RunJoin_SourceSelectionContract.selectedRecord d x w) = ok records →
      BuilderSpendRelation.RspendPlus
        (mapPub («K» := K) (PV_Src_Public.canonicalPublic
          (publicInput (PV_RunJoin_SourceSelectionContract.selectedRecord d x w))))
        (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))) :
    @PV_RunJoin_SelectedAdmission.Remainder actualExternal actualRecords CommitHandle d x where
  compile_call := compile_call
  words := (words_and_public actualExternal actualRecords external_eq records_eq d x
    canonical selected_eq compile_call).1
  publicCorr := (words_and_public actualExternal actualRecords external_eq records_eq d x
    canonical selected_eq compile_call).2
  admission := admission

#print axioms words_and_public
#print axioms remainder
end R1Z.PV_RunJoin_SelectedSourceReduction
