import R1Z.PV_RunJoin_ConstantCallback16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CallbackRounds16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds
variable {K F : Type} [Field K] [CharP K 2147483647]

theorem initial (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace))
    (s input : State) (round : U8) (hs : Canonical s) :
    ∃ out : Output F,
      poseidon2.permute_optimized_with_trace_loop0
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
        ⟨⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩,0#usize⟩ s trace round input = ok out ∧
      Canonical out.1 ∧ out.2.1 = trace ∧
      liftA (K := K) out.1 = PV_Src_PortFullMeaning.model
        (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_INITIAL.val 0#usize) (liftA s) := by
  obtain ⟨out,ho,hcan,hmean⟩ := PV_Src_PortInitialResult.source (K := K) s input () round hs
  refine ⟨PV_RunJoin_ConstantCallback16.replace trace out,?_,hcan,rfl,hmean⟩
  rw [PV_Src_PortConstantInstance.initial_source callback s input trace round hs]
  apply PV_RunJoin_ConstantCallback16.full callback trace hc
  rw [← PV_Src_PortConstantInstance.initial_source PV_Src_PortNoop.callback s input () round hs]
  exact ho

theorem internal (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace))
    (s input : State) (round : U8) (hs : Canonical s) :
    ∃ out : Output F,
      poseidon2.permute_optimized_with_trace_loop1 callback
        ⟨poseidon2.INTERNAL.val,0#usize⟩ s trace round input = ok out ∧
      Canonical out.1 ∧ out.2.1 = trace ∧
      liftA (K := K) out.1 = PV_Src_PortInternalMeaning.model
        (PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) (liftA s) := by
  obtain ⟨out,ho,hcan,hmean⟩ := PV_Src_PortInternalResult.source (K := K) s input () round hs
  refine ⟨PV_RunJoin_ConstantCallback16.replace trace out,?_,hcan,rfl,hmean⟩
  rw [PV_Src_PortConstantInstance.internal_source callback s input trace round hs]
  apply PV_RunJoin_ConstantCallback16.internal callback trace hc
  rw [← PV_Src_PortConstantInstance.internal_source PV_Src_PortNoop.callback s input () round hs]
  exact ho

theorem final_rounds (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace))
    (s input : State) (round : U8) (hs : Canonical s) :
    ∃ out : State,
      poseidon2.permute_optimized_with_trace_loop2
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
        ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ s trace round input = ok (out,trace) ∧
      Canonical out ∧
      liftA (K := K) out = PV_Src_PortFullMeaning.model
        (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_FINAL.val 0#usize) (liftA s) := by
  obtain ⟨out,ho,_⟩ := PV_Src_PortNoopFull.total
    (fun i => poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 i))
    (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_FINAL.val 0#usize) s input () round
  refine ⟨out.1,?_,?_,?_⟩
  · rw [PV_Src_PortConstantInstance.final_source callback s input trace round hs,
      PV_RunJoin_ConstantCallback16.full callback trace hc _ _ s input round out ho]
    rfl
  · exact PV_Src_PortTraceCanonical.full _ _ _ s input () round hs out ho
  · exact PV_Src_PortFullMeaning.meaning _ _ s input () round out ho
#print axioms initial
#print axioms internal
#print axioms final_rounds
end R1Z.PV_RunJoin_CallbackRounds16
