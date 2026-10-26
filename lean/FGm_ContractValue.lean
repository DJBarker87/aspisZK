import FGm_ContractStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_ContractValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode)
open FGm_ContractStep (State Inv prefixSum measure)

theorem value (low : Array NE 16#usize) (cs : Array NE 12#usize) (out : NE)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1
      {start:=0#usize,«end»:=12#usize} low cs
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decode out=prefixSum low cs 12 := by
  apply FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2)
    (Inv low cs) (fun z => FIo_WideValues.Canon z ∧ decode z=prefixSum low cs 12)
    measure (fun s h out hr => by cases out <;> exact FGm_ContractStep.step low cs hlow hcs s h _ hr)
    ({start:=0#usize,«end»:=12#usize},FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) out ?_ run
  exact ⟨rfl,by decide,FIo_Constants.zero.1,by simpa [prefixSum] using FIo_Constants.zero.2⟩

#print axioms value
end AspisR1.FGm_ContractValue
end
