import RPu_FJc_InactiveCoefficientsStep
import RPu_FJc_ZeroArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveCoefficientsValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FJc_InactiveCoefficientsStep

theorem loop (f : Slice U8) (stop : Nat) (initial : Nat → AspisWideTower.WideExact)
    (iter : FIo_RangeNext.Range) (cs out : FIo_GroupCoefficients.Cs)
    (inv : Inv f stop initial (iter,cs))
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0 iter f cs=ok out) : Post f stop initial out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2)
    (Inv f stop initial) (Post f stop initial) FIo_GroupCoefficients.measure
    (fun s h r hr=>by cases r <;> exact step f stop initial s h _ hr)
    (iter,cs) out inv run

theorem sixtyfour (f : Slice U8) (out : FIo_GroupCoefficients.Cs)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0
      {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok out) :
    FIo_ArrayCanon.Holds out ∧ ∀ g,FIp_ArrayValue.value out g=FJc_InactiveCoefficientsModel.sumPrefix f g 64 := by
  have h := loop f 64 (fun _=>0) _ _ out
    ⟨FIo_GroupCanonical.zeros _,rfl,by decide,by decide,by
      intro g
      change FIp_ArrayValue.value (Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) g=0+0
      simpa only [add_zero] using FJc_ZeroArray.value 12#usize g⟩ run
  exact ⟨h.1,fun g=>by simpa only [zero_add] using h.2 g⟩
#print axioms loop
#print axioms sixtyfour
end AspisR1.FJc_InactiveCoefficientsValue
end
