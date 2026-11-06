import NIW_AlignRegularPhaseSource
import NIW_AlignRegularPostBoundary
import NIW_AlignCommonSource
import NIW_AlignPartialPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_RegularCut
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

/-- Oracle replies are DATA, with no clause asserting a child endpoint. Full
mutable values are retained even when the Rust Result is Err. The selected
native windows are lifted extensionally, as in NIW_AlignFrames. -/
structure Log where
 regular : Result NHM_RegularKinds.Reply
 common : Result (W × CommonCells)
 partialReply : Result RP
 high : Result (RU × Parts)

abbrev State := RU × Scratch × Parts

/-- G for the corrected borrowed-slice regular/shared stage (weights.rs:279-288).
Every entered outer fail/div is terminal; unreached log fields are ignored. -/
def G (shared : Bool) (l : Log) : Result State × List Nat :=
 match l.regular with
 | fail err => (fail err,[0])
 | div => (div,[0])
 | ok (reply,scratch,parts) => match reply with
   | .Err err => (ok (.Err err,scratch,parts),[0])
   | .Ok _ => if shared then
     match l.common with
     | fail err => (fail err,[0,1])
     | div => (div,[0,1])
     | ok _ => match l.partialReply with
       | fail err => (fail err,[0,1,2])
       | div => (div,[0,1,2])
       | ok (.Err err) => (ok (.Err err,scratch,parts),[0,1,2])
       | ok (.Ok _) => match l.high with
         | fail err => (fail err,[0,1,2,3])
         | div => (div,[0,1,2,3])
         | ok (reply,after) => (ok (reply,scratch,after),[0,1,2,3])
    else (ok (.Ok (),scratch,parts),[0])

/-- The complete ordinary Rust-returning cut, with full scratch and Parts
post-values. No claim about an opaque oracle's implementation is in this cut.
Native association remains a reviewed P6/D188 transcription. -/
def returningCut (shared : Bool) (l : Log) (out : Result State) (events : List Nat) : Prop :=
 (out,events)=G shared l

/-- A native cut is universally quantified over replies; specialization does
not require an inverse association from an independent raw log. -/
theorem specialize (shared : Bool) (l : Log) (out : Result State) (events : List Nat)
 (cut : returningCut shared l out events) : (out,events)=G shared l := cut

/-- Every early regular rejection returns its own mutated scratch and Parts;
no partial/high reply is inspected. -/
theorem regular_error (l : Log) (err : verifier.Error) (scratch : Scratch) (parts : Parts)
 (reply : l.regular=ok (.Err err,scratch,parts)) (shared : Bool) :
 G shared l=(ok (.Err err,scratch,parts),[0]) := by
 simp only [G,reply]

#print G
#print axioms specialize
#print axioms regular_error
end AspisR1.NJF_RegularCut
