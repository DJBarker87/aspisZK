import NJX_RangeInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RangeFrame
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_RangeStep (State)
/-- Actual raw33cell frame: every source range iteration touches only0..29.
In particular slots30/31/32 remain the original ZERO until explicit tail writes. -/
theorem frame {view : Fin 3} {xs : Fin 10 → NQ} {is : List (Fin 10)} {before after : State}
 (trace : NJX_RangeFold.Trace view xs is before after) (j : Fin 33) (hj : 30≤j.val) : after j=before j := by
 induction trace with
 | nil s=>rfl
 | @cons i is before middle after call frames rest ih=>
   rw [ih,frames j]
   apply if_neg
   intro same
   have hidx : (NJX_RangeStep.index view i).val<30 := by
    dsimp only [NJX_RangeStep.index]
    have hv:=view.isLt
    have hi:=i.isLt
    omega
   have vals:=congrArg Fin.val same
   omega

/-- ZERO initialization is retained at all3future reconstruction/tail slots
on the SAME complete3×10invocation, not on independently chosen states. -/
theorem source (o : NJX_RangeInvocation.Openings) (hz : FIw_ArrayValue.canonical o.z)
 (hs : FIw_ArrayValue.canonical o.succ_z) (hx : FIw_ArrayValue.canonical o.xor12_z) :
 ∃ a b c,
 NJX_RangeFold.Trace 0 (NJX_RangeInvocation.xs o 0) (List.finRange 10) NJX_RangeInvocation.zero a ∧
 NJX_RangeFold.Trace 1 (NJX_RangeInvocation.xs o 1) (List.finRange 10) a b ∧
 NJX_RangeFold.Trace 2 (NJX_RangeInvocation.xs o 2) (List.finRange 10) b c ∧
 (∀ j,Canon (c j)) ∧ ∀ j : Fin 33,30≤j.val→c j=FIq_Native.field.QM31.ZERO := by
 obtain ⟨a,b,c,_,ta,_,tb,_,tc,hc⟩ := NJX_RangeInvocation.source o hz hs hx
 refine ⟨a,b,c,ta,tb,tc,hc,?_⟩
 intro j hj
 rw [frame tc j hj,frame tb j hj,frame ta j hj]
 rfl
#print source
#print axioms frame
#print axioms source
end AspisR1.NJX_RangeFrame
end
