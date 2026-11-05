import NHX_FinalLoop
import NHX_LowDomain
set_option autoImplicit false
namespace NIG_BothBranches
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Aeneas duplicates the one native two-fold tail beneath the shared guard.
Both copies use precisely the SAME arguments and step body. -/
theorem low_step (ap0 ap1:NHX_LowDomain.Powers) (s:NHX_LowDomain.State) :
 FIo_Native.weights.Weights.pair_loop7.body ap0 ap1 s.1 s.2=
 FIo_Native.weights.Weights.pair_loop15.body ap0 ap1 s.1 s.2 := rfl

theorem low (ap0 ap1:NHX_LowDomain.Powers) (s:NHX_LowDomain.State) :
 FIo_Native.weights.Weights.pair_loop7 s.1 ap0 ap1 s.2=
 FIo_Native.weights.Weights.pair_loop15 s.1 ap0 ap1 s.2 := rfl

theorem libra_step (f:Slice U8) (libra:Array NE 4#usize)
 (iter:core.ops.range.Range Usize) (parts:Array NE 7#usize) :
 FIo_Native.weights.Weights.pair_loop8.body f libra iter parts=
 FIo_Native.weights.Weights.pair_loop16.body f libra iter parts := rfl

theorem libra (f:Slice U8) (libra:Array NE 4#usize)
 (iter:core.ops.range.Range Usize) (parts:Array NE 7#usize) :
 FIo_Native.weights.Weights.pair_loop8 iter f parts libra=
 FIo_Native.weights.Weights.pair_loop16 iter f parts libra := rfl

theorem final_step (parts powers:NHX_FinalLoop.Cells) (s:NHX_FinalLoop.State) :
 FIo_Native.weights.Weights.pair_loop9.body parts powers s.1 s.2=
 FIo_Native.weights.Weights.pair_loop17.body parts powers s.1 s.2 := rfl

theorem final (parts powers:NHX_FinalLoop.Cells) (s:NHX_FinalLoop.State) :
 FIo_Native.weights.Weights.pair_loop9 s.1 parts powers s.2=
 FIo_Native.weights.Weights.pair_loop17 s.1 parts powers s.2 := rfl
#print axioms low_step
#print axioms low
#print axioms libra_step
#print axioms libra
#print axioms final_step
#print axioms final
end NIG_BothBranches
