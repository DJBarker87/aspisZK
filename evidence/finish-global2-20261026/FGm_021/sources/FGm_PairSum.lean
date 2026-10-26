import FGm_PairSumStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PairSum
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode)
open FGm_PairSumStep (State Inv prefixSum measure)

theorem value (parts k : Array NE 7#usize) (out : NE)
    (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_ArrayCanon.Holds k)
    (run : FIo_Native.weights.Weights.pair_loop9
      {start:=0#usize,«end»:=7#usize} parts k
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decode out=prefixSum parts k 7 := by
  apply FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.Weights.pair_loop9.body parts k s.1 s.2)
    (Inv parts k) (fun z => FIo_WideValues.Canon z ∧ decode z=prefixSum parts k 7)
    measure (fun s h out hr => by cases out <;> exact FGm_PairSumStep.step parts k hp hk s h _ hr)
    ({start:=0#usize,«end»:=7#usize},FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) out ?_ run
  exact ⟨rfl,by decide,FIo_Constants.zero.1,by simpa [prefixSum] using FIo_Constants.zero.2⟩

#print axioms value
end AspisR1.FGm_PairSum
end
