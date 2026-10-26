import R1Z.PV_Src_FrozenPublic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedSourceCore
open Aeneas Aeneas.Std Result R0P R0Z.ZkStatement R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_Forest_PrimitiveArguments PV_Src_NativeInput
variable {K W : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Two source joins remain indispensable: the actual dictionaries must equal
these owned references, and the actual selected record must equal the encoded
canonical record. Neither equality follows from the record's type or name. -/
theorem words_and_public
    (actualExternal : ExternalLinear) (actualRecords : Records)
    (external_eq : actualExternal = PV_Src_FrozenInput.external)
    (records_eq : actualRecords = PV_Src_FrozenInput.records)
    (selected : W → PV_Src_NativeInput.Input)
    (canonical : W →
      PV_Src_FrozenInput.Data (K := K))
    (selected_eq : ∀ w, selected w =
      PV_Src_FrozenInput.input (canonical w))
    (compile_call : ∀ w,
      @run actualExternal actualRecords (selected w) =
        ok (.Ok (selected w).compiled)) :
    (∀ w records,
      @newRecords actualRecords (selected w) = ok records →
        WitnessOk (wordWitness records.w)) ∧
    (∀ w records,
      @newRecords actualRecords (selected w) = ok records →
        PubCorr (wordPublic records.p)
          (mapPub (K := K) (PV_Src_Public.canonicalPublic
            (publicInput (selected w))))) := by
  cases external_eq
  cases records_eq
  constructor
  · intro w records hr
    rw [selected_eq w] at hr
    exact PV_Src_FrozenInput.words (canonical w) records hr
  · intro w records hr
    have hc := compile_call w
    rw [selected_eq w] at hc hr ⊢
    exact PV_Src_FrozenPublic.correspondence (canonical w) hc records hr


#print axioms words_and_public
end R1Z.PV_RunJoin_SelectedSourceCore
