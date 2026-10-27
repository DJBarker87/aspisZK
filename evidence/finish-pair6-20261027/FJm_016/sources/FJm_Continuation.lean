import FJj_RegularFrame
import FJg_SharedHighTrace
import FJc_LibraFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_Continuation
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)

/-- Shared original/absorption writes preserve each other part. -/
theorem shared (w : FIo_Native.weights.Weights) (partials ap0 ap1 : Array NE 4#usize)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials w ap0 ap1 before=ok (.Ok (),after))
    (j : Nat) (h1 : j≠1) (h3 : j≠3) :
    FIp_ArrayValue.value after j=FIp_ArrayValue.value before j := by
  obtain ⟨row,coeff,low0,low1,high,s0,s1,scale,value,old,absorption,back,
    hr,h4,hh,h0,hs0,h1r,hs1,hm,hv,hb,hu⟩ :=
    FJg_SharedHighTrace.reached w partials ap0 ap1 before after run
  rw [FJc_ArrayUpdateValue.value (back value) after 3#usize absorption j hu,
    if_neg (by simpa using Ne.symm h3),FIp_ArraySetValue.back before 1#usize old back hb]
  exact FIp_ArraySetValue.other before 1#usize value j (by simpa using Ne.symm h1)

/-- The actual inactive write and Libra loop preserve a regular part. -/
theorem tail (f : Slice U8) (libra : Array NE 4#usize)
    (highParts lowParts parts : Array NE 7#usize) (inactive : NE)
    (hu : Array.update highParts 0#usize inactive=ok lowParts)
    (hl : FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f lowParts libra=ok parts)
    (j : Nat) (h0 : j≠0) (h4 : j≠4) :
    FIp_ArrayValue.value parts j=FIp_ArrayValue.value highParts j := by
  rw [FJc_LibraFrame.value f libra lowParts parts _ hl j h4,
    FJc_ArrayUpdateValue.value highParts lowParts 0#usize inactive j hu,
    if_neg (by simpa using Ne.symm h0)]

#print axioms shared
#print axioms tail
end AspisR1.FJm_Continuation
end
