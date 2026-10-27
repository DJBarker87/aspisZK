import RPu_FGm_SubsetStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_SubsetValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode)
open FGm_SubsetStep (State Inv prefixSum measure)

theorem value (low : Array NE 16#usize) (group : Usize) (out : NE)
    (hlow : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0
      {start:=0#usize,«end»:=16#usize} low group
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decode out=prefixSum low group 16 := by
  apply FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2)
    (Inv low group) (fun z => FIo_WideValues.Canon z ∧ decode z=prefixSum low group 16)
    measure (fun s h out hr => by cases out <;> exact FGm_SubsetStep.step low group hlow s h _ hr)
    ({start:=0#usize,«end»:=16#usize},FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) out ?_ run
  exact ⟨rfl,by decide,FIo_Constants.zero.1,by simpa [prefixSum] using FIo_Constants.zero.2⟩

#print axioms value
end AspisR1.FGm_SubsetValue
end
