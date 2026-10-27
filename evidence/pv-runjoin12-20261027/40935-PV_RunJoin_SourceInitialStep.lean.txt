import R1Z.PV_Src_PortFullRoundCopy
/-! Proof draft reused read-only from srcid d597d31545. This new module is checked independently; no upstream draft is assumed compiled. -/

/-! Exact source trace-loop step. Callback errors and state changes remain
in the Result expression; the body alone is replaced by its proved copy. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceInitialStep
open Aeneas Aeneas.Std Result
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (iter after : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 16#usize)))
    (s input : State) (trace : F) (round : U8) (index : Usize) (c : State)
    (hn : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (Array U32 16#usize)) iter =
      ok (some (index,c),after))
    (hs : Canonical s) (hc : Canonical c) :
    poseidon2.permute_optimized_with_trace_loop0 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter s trace round input =
      (do
        let out ← R0PoseidonCopy.full_round s c
        let (_,trace1) ← callback.call_mut trace
          ({round,kind := poseidon2.Poseidon2RoundKind.ExternalInitial (UScalar.cast .U8 index),
            input,output := out} : poseidon2.Poseidon2RoundTransition)
        poseidon2.permute_optimized_with_trace_loop0 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback after out trace1
          (U8.wrapping_add round 1#u8) out) := by
  letI : ExternalLinear := PV_Src_ExternalReference.dictionary
  rw [poseidon2.permute_optimized_with_trace_loop0,hn]
  simp only [bind_tc_ok,lift]
  have he := congrArg (fun body : Result State => do
    let out ← body
    let (_,trace1) ← callback.call_mut trace
      ({round,kind := poseidon2.Poseidon2RoundKind.ExternalInitial (UScalar.cast .U8 index),
        input,output := out} : poseidon2.Poseidon2RoundTransition)
    poseidon2.permute_optimized_with_trace_loop0 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback after out trace1
      (U8.wrapping_add round 1#u8) out)
    (PV_Src_PortFullRoundCopy.initial s c hs hc)
  simp only [PV_Src_PortFullRoundModel.initial,bind_assoc_eq,lift,bind_tc_ok] at he
  convert he using 1 <;> rfl

#print axioms source
end R1Z.PV_RunJoin_SourceInitialStep
