import FIp_PowersStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PowersValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FIp_PowersState

theorem loop_value {N : Usize} (x : NE) (hx : FIo_WideValues.Canon x)
    (s : State N) (result : Array NE N) (inv : Inv x s)
    (run : FIo_Native.weights.powers_loop x s.1 s.2.1 s.2.2=ok result) : Post x result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State N => FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2)
    (Inv x) (Post x) FIo_PowersCanonical.measure
    (fun s h out hr => by cases out <;> exact FIp_PowersStep.step x hx s h _ hr)
    s result inv run

theorem powers (N : Usize) (x : NE) (result : Array NE N) (hx : FIo_WideValues.Canon x)
    (run : FIo_Native.weights.powers N x=ok result) : Post x result := by
  unfold FIo_Native.weights.powers at run
  apply loop_value x hx (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,0#usize) result ?_ run
  refine ⟨⟨FIo_GroupCanonical.zeros N,FIo_Constants.one.1⟩,?_,?_,?_⟩
  · change 0≤N.val; exact Nat.zero_le _
  · change decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ONE)=decodeWide (wide x)^0
    rw [FIo_Constants.one.2,pow_zero]
  · intro j hj
    change j<0 at hj
    omega

#print axioms loop_value
#print axioms powers
end AspisR1.FIp_PowersValue
end
