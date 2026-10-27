import R1Z.PV_Src_PortThreadedResult
import R1Z.PV_Src_PortFullFold
import R1Z.PV_Src_PortInternalFold
import R1Z.PV_Src_PortInitialList
import R1Z.PV_Src_PortInternalList
import R1Z.PV_Src_PortFinalList
set_option autoImplicit false
namespace R1Z.PV_Src_PortPermutation
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
variable {K : Type} [Field K] [CharP K 2147483647]

theorem model (s : Fin 16 → K) : PV_Src_PortThreadedResult.model s = R0P.poseidonPermutation s := by
  simp only [PV_Src_PortThreadedResult.model,PV_Src_PortFullFold.pairs,PV_Src_PortInternalFold.pairs,
    PV_Src_PortInitialList.source,PV_Src_PortInternalList.source,PV_Src_PortFinalList.source]
  rfl

theorem source (s : State) : ∃ out : State,
    poseidon2.permute_optimized_with_trace
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_Src_PortNoop.callback s () = ok out ∧
    Canonical out ∧ liftA (K := K) out = R0P.poseidonPermutation (liftA s) := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_PortThreadedResult.source (K := K) s
  refine ⟨out.1,?_,hc,?_⟩
  · rw [poseidon2.permute_optimized_with_trace,ho]
    rfl
  · exact hm.trans (model _)

#print axioms model
#print axioms source
end R1Z.PV_Src_PortPermutation
