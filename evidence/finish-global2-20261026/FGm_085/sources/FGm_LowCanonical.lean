import FGm_LowStepCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_LowCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_LowStepCanonical (State measure)

theorem loop (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1)
    (iter : FIo_RangeNext.Range) (low out : Array NE 16#usize)
    (initial : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.Weights.pair_loop7 iter ap0 ap1 low=ok out) :
    FIo_ArrayCanon.Holds out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.Weights.pair_loop7.body ap0 ap1 s.1 s.2)
    (fun s => FIo_ArrayCanon.Holds s.2) FIo_ArrayCanon.Holds measure
    (fun s h out hr => by cases out <;> exact FGm_LowStepCanonical.step ap0 ap1 ha0 ha1 s h _ hr)
    (iter,low) out initial run

theorem other_loop : FIo_Native.weights.Weights.pair_loop15=FIo_Native.weights.Weights.pair_loop7 := rfl

#print axioms loop
#print axioms other_loop
end AspisR1.FGm_LowCanonical
end
