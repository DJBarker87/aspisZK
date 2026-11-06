import NKF_LaneFactor
import NKF_LaneConstructor
import NKF_LanePrefix
set_option autoImplicit false
noncomputable section
namespace NKP_LaneCuts
open Aeneas Aeneas.Std Result
abbrev Node := NKF_LaneTrace.Node
abbrev Frontier := NKF_LaneTrace.Frontier
abbrev Reply := NKF_LaneTrace.Reply
attribute [local instance] Classical.propDecidable

/-- Typed transcription of the four factored NKP_lane.py iteration windows.
The byte/reply cut is separately recorded at field0; field1 supplies the
selected assignment/error frame, field2 the untouched coordinate, field3 the
exact post-assignment guard Result. These are native cut propositions, not
an assumed equality of a whole native loop with its model. -/
structure IterationCut {F : Type} (empty : Node) (occupied : Bool)
 (before after : Frontier) (level : Fin 20)
 (raw : core.result.Result Node F) (returned : Reply) : Prop where
 result : returned = match raw with
   | .Err _ => .Err .InvalidAccountData
   | .Ok node => NKF_LaneFactor.guard empty node occupied
 selected : ∀ word : Fin 8, after level word = match raw with
   | .Err _ => before level word
   | .Ok node => node word
 frame : ∀ other : Fin 20, other ≠ level → ∀ word : Fin 8,
   after other word = before other word

/-- The source iterator's selected and untouched windows reconstruct its
complete frontier, including the write that precedes a later rejection. -/
theorem iteration {F : Type} (empty : Node) (occupied : Bool)
 (before after : Frontier) (level : Fin 20)
 (raw : core.result.Result Node F) (returned : Reply)
 (cut : IterationCut empty occupied before after level raw returned) :
 (returned,after) = NKF_LaneTrace.iteration empty occupied before level raw := by
 cases raw with
 | Err e =>
   have state : after = before := by
    funext other word
    by_cases h : other = level
    · subst other; exact cut.selected word
    · exact cut.frame other h word
   rw [cut.result,state]
   rfl
 | Ok node =>
   have state : after = NJD_LaneStep.write before level node := by
    funext other word
    by_cases h : other = level
    · subst other
      simpa [NJD_LaneStep.write] using cut.selected word
    · simpa [NJD_LaneStep.write,h] using cut.frame other h word
   rw [cut.result,state,NKF_LaneFactor.success_step]

/-- Constructor fields are reconstructed by the already checked NKF proof;
no new equality is postulated for the returned record. Native controls for
all six fields are tracked independently in NKP_LANE_RESULTS.json. -/
theorem constructor (before after : NKF_LaneConstructor.Lane)
 (cut : NKF_LaneConstructor.Fields before after) : before = after :=
 NKF_LaneConstructor.constructor before after cut

/-- Exact absolute wire offset of the native digest-call window. The lane
header is80bytes and each tree node32bytes; no concrete table reduction. -/
theorem absolute_window (level byte : Nat) (hl : level < 20) (hb : byte < 32) :
 80 + (48 + 32*level + byte) = 128 + 32*level + byte ∧
 80 + (48 + 32*level + byte) < 768 := by omega

#print axioms iteration
#print axioms constructor
#print axioms absolute_window
end NKP_LaneCuts
