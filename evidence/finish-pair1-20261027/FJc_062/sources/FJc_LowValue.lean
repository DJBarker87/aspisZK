import FJc_LowStep
import FIo_GroupCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FJc_LowStep

theorem loop (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1)
    (iter : FIo_RangeNext.Range) (low out : Array NE 16#usize)
    (inv : Inv ap0 ap1 (iter,low))
    (run : FIo_Native.weights.Weights.pair_loop15 iter ap0 ap1 low=ok out) : Post ap0 ap1 out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.Weights.pair_loop15.body ap0 ap1 s.1 s.2)
    (Inv ap0 ap1) (Post ap0 ap1) measure
    (fun s h r hr=>by cases r <;> exact step ap0 ap1 ha0 ha1 s h _ hr)
    (iter,low) out inv run

theorem sixteen (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1) (out : Array NE 16#usize)
    (run : FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
      (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok out) :
    FIo_ArrayCanon.Holds out ∧ ∀ j,j<16 → FIp_ArrayValue.value out j=FJc_LowModel.value ap0 ap1 j := by
  exact loop ap0 ap1 ha0 ha1 _ _ out
    ⟨FIo_GroupCanonical.zeros _,rfl,by decide,by intro j hj;change j<0 at hj;omega⟩ run

theorem seven_alias (iter : FIo_RangeNext.Range) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize) :
    FIo_Native.weights.Weights.pair_loop7 iter ap0 ap1 low=
      FIo_Native.weights.Weights.pair_loop15 iter ap0 ap1 low := rfl
#print axioms loop
#print axioms sixteen
#print axioms seven_alias
end AspisR1.FJc_LowValue
end
