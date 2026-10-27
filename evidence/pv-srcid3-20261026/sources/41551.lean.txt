import R1Z.PV_Src_PortInternalRoundCopy

/-! Exact source trace-loop step. Callback errors and state changes remain
in the Result expression; the body alone is replaced by its proved copy. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalRoundStep
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (iter after : core.iter.adapters.enumerate.Enumerate (core.array.iter.IntoIter U32 14#usize))
    (s input : State) (trace : F) (round : U8) (index : Usize) (c : U32)
    (hn : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator U32 14#usize) iter =
      ok (some (index,c),after))
    (hs : Canonical s) (hc : c.val < 2147483647) :
    poseidon2.permute_optimized_with_trace_loop1 callback iter s trace round input =
      (do
        let out ← R0PoseidonCopy.internal_round s c R0PoseidonCopy.INTERNAL_SHIFTS
        let (_,trace1) ← callback.call_mut trace
          ({round,kind := poseidon2.Poseidon2RoundKind.Internal (UScalar.cast .U8 index),
            input,output := out} : poseidon2.Poseidon2RoundTransition)
        poseidon2.permute_optimized_with_trace_loop1 callback after out trace1
          (U8.wrapping_add round 1#u8) out) := by
  rw [poseidon2.permute_optimized_with_trace_loop1,hn]
  simp only [bind_tc_ok,lift]
  have he := congrArg (fun body : Result State => do
    let out ← body
    let (_,trace1) ← callback.call_mut trace
      ({round,kind := poseidon2.Poseidon2RoundKind.Internal (UScalar.cast .U8 index),
        input,output := out} : poseidon2.Poseidon2RoundTransition)
    poseidon2.permute_optimized_with_trace_loop1 callback after out trace1
      (U8.wrapping_add round 1#u8) out)
    (PV_Src_PortInternalRoundCopy.source s c hs hc)
  simpa only [PV_Src_PortInternalRoundCopy.run,bind_assoc_eq,lift,bind_tc_ok] using he

#print axioms source
end R1Z.PV_Src_PortInternalRoundStep
