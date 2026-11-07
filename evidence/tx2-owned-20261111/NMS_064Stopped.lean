import NMN_064
import NMS_Continuation
set_option autoImplicit false
noncomputable section
namespace NMS_064Stopped
open Aeneas Aeneas.Std AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The existing candidate's independent C04 arm is carried intact at SAME
args. No assertion that the ideal source fails and no returned child Result. -/
theorem from_candidate {Ambient X : Type} (H : Bytes → State) (frame : Frame Ambient X)
 (domain : NMN_064.Domain frame.args)
 (records : List (NLT_NativeInvocation.Occurrence H frame.args.digest frame.args.hash))
 (cut : NLT_C04Stop.Cut H) (events : List (Event Ambient X))
 (native : NMN_064.Native H frame (.common (.c04Stopped records cut)) events) :
 NLT_CompleteRoot.StoppedLaw H frame.args.digest frame.args.publicBytes frame.args.proof
  frame.args.checkpoint frame.args.hash records cut ∧
 events = chronology H frame (.common (.c04Stopped records cut)) :=
 (NMN_064.root H frame domain).1 _ _ native

/-- Once this native stop occurs the parent cannot run error-map or emit.
Its only output is the exact prefix with the SAME pending C04 cut. -/
theorem no_suffix {W E : Type} (H : Bytes → State) (prefix : List E)
 (cut : NLT_C04Stop.Cut H)
 (suffix : Unit → W → NMS_Continuation.Outcome W E Unit (NLT_C04Stop.Cut H)) :
 NMS_Continuation.bind
  (.stopped prefix cut : NMS_Continuation.Outcome W E Unit (NLT_C04Stop.Cut H)) suffix =
 .stopped prefix cut := rfl
#print from_candidate
#print axioms from_candidate
#print axioms no_suffix
end NMS_064Stopped
