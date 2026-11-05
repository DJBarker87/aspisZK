import NIW_AlignBoundary
import NIT_GuardFrontJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignControl
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignBoundary Classical

def erasePartial (r : Reply Powers) : Reply Unit :=
 match r with | .Err e=>.Err e | .Ok _=>.Ok ()

/-- A view of the SAME observed replies, not a selected model call result. -/
def skeleton (shared : Bool) (l : Log) : SameGuard :=
 ⟨shared,l.regular,erasePartial l.partialReply,l.high,l.events,l.count⟩

def countBase (shared : Bool) (l : Log) : Nat :=
 if ¬enteredPartial shared l then 1 else if ¬enteredHigh shared l then 3 else 4

theorem expected_reply (shared : Bool) (l : Log) :
 (sameExpected shared (skeleton shared l)).1=expected shared l := by
 cases shared <;> cases hr : l.regular <;> cases hp : l.partialReply <;> cases hh : l.high <;>
  simp [sameExpected,skeleton,expected,erasePartial,hr,hp,hh]

theorem expected_count (shared : Bool) (l : Log) :
 (sameExpected shared (skeleton shared l)).2=
 countBase shared l + if expected shared l=.Ok () then 1 else 0 := by
 cases shared <;> cases hr : l.regular <;> cases hp : l.partialReply <;> cases hh : l.high <;>
  simp [sameExpected,skeleton,expected,erasePartial,countBase,enteredPartial,enteredHigh,hr,hp,hh]

#print axioms expected_reply
#print axioms expected_count
end AspisR1.NIW_AlignControl
