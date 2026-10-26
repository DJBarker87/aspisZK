import FGm_PowersStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PowersValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_PowersStep (State Inv Post measure)

theorem value (N : Usize) (x : NE) (result : Array NE N)
    (hx : FIo_WideValues.Canon x)
    (run : FIo_Native.weights.powers N x=ok result) : Post x result := by
  apply FIo_LoopInvariant.preserve
    (fun s : State N => FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2)
    (Inv x) (Post x) measure
    (fun s h out hr => by cases out <;> exact FGm_PowersStep.step x hx s h _ hr)
    (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,
      FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,0#usize) result ?_ run
  refine ⟨FIo_GroupCanonical.zeros N,FIo_Constants.one.1,?_,?_⟩
  · change FGm_ArrayValue.decode FIo_Native.aspis_core.field.wide_exact.WideExact.ONE = FGm_ArrayValue.decode x^0
    simpa only [pow_zero] using FIo_Constants.one.2
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)

#print axioms value
end AspisR1.FGm_PowersValue
end
