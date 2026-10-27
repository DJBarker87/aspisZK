import R1Z.PV_Src_PortInternalMeaning
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalResult
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds
variable {K : Type} [Field K] [CharP K 2147483647]

theorem source (s input : State) (trace : Unit) (round : U8) (hs : Canonical s) :
    ∃ out : Output Unit,
      poseidon2.permute_optimized_with_trace_loop1 PV_Src_PortNoop.callback
        ⟨poseidon2.INTERNAL.val,0#usize⟩ s trace round input = ok out ∧
      Canonical out.1 ∧
      liftA (K := K) out.1 = PV_Src_PortInternalMeaning.model
        (PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) (liftA s) := by
  obtain ⟨out,ho,_⟩ := PV_Src_PortNoopInternal.total
    (PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) s input trace round
  refine ⟨out,?_,?_,?_⟩
  · rw [PV_Src_PortConstantInstance.internal_source _ s input trace round hs]
    exact ho
  · exact PV_Src_PortTraceCanonical.internal _ _ s input trace round hs out ho
  · exact PV_Src_PortInternalMeaning.meaning _ s input trace round out ho

#print axioms source
end R1Z.PV_Src_PortInternalResult
