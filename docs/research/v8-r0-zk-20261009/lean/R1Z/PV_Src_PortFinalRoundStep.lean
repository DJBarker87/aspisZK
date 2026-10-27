import R1Z.PV_Src_PortFullRoundCopy

/-! Exact source trace-loop step. Callback errors and state changes remain
in the Result expression; the body alone is replaced by its proved copy. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortFinalRoundStep
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (iter after : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 16#usize)))
    (s input : State) (trace : F) (round : U8) (index : Usize) (c : State)
    (hn : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (Array U32 16#usize)) iter =
      ok (some (index,c),after))
    (hs : Canonical s) (hc : Canonical c) :
    poseidon2.permute_optimized_with_trace_loop2 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter s trace round input =
      (do
        let out ← R0PoseidonCopy.full_round s c
        let (_,trace1) ← callback.call_mut trace
          ({round,kind := poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 index),
            input,output := out} : poseidon2.Poseidon2RoundTransition)
        poseidon2.permute_optimized_with_trace_loop2 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback after out trace1
          (U8.wrapping_add round 1#u8) out) := by
  rw [poseidon2.permute_optimized_with_trace_loop2,hn]
  simp only [bind_tc_ok,lift]
  change (do
    let out ← PV_Src_PortFullRoundModel.final_round s c
    let (_,trace1) ← callback.call_mut trace
      ({round,kind := poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 index),
        input,output := out} : poseidon2.Poseidon2RoundTransition)
    poseidon2.permute_optimized_with_trace_loop2 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback after out trace1
      (U8.wrapping_add round 1#u8) out) = _
  rw [PV_Src_PortFullRoundCopy.final_round s c hs hc]

#print axioms source
end R1Z.PV_Src_PortFinalRoundStep
