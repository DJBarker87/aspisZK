import NGW_DotCodec
import NHE_FieldPort
import SAG_DotClosed
set_option autoImplicit false
namespace NHE_DotState
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NGM_DotABI.Dot
abbrev Push := AspisR1FinishDotSourceABI.PushState

def toPush (d : Dot) : Push := ⟨⟨d.c0.sums⟩,⟨d.c1.sums⟩,d.count⟩
def fromPush (d : Push) : Dot := ⟨⟨d.c0.sums⟩,⟨d.c1.sums⟩,d.count⟩

theorem from_to (d : Dot) : fromPush (toPush d)=d := by cases d; rfl
theorem to_from (d : Push) : toPush (fromPush d)=d := by cases d; rfl

theorem new :
 FIo_FieldBridge.map toPush FIo_Native.fast_pairing.EbyKDot.new=
 AspisR1FinishDotConcreteOps.sourceNewDot := by
 rw [AspisR1FinishDotConcreteOps.sourceNewDot_zero]
 simp only [FIo_Native.fast_pairing.EbyKDot.new,FIo_Native.fast_pairing.canonical.Dot.new,bind_tc_ok]
 rfl

#print axioms from_to
#print axioms to_from
#print axioms new
end NHE_DotState
