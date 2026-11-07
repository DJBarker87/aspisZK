import NMN_OracleFold
import NHV_ReleaseOps
set_option autoImplicit false
noncomputable section
namespace NMN_Observer
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The deployed profiling hook returns unit without a semantic event. -/
theorem marker : NHV_ReleaseOps.mark none .Parsed = .ok () := rfl
/-- Marker is a source call site; its erasure is not a digest or runtime event. -/
def erase {Ambient X : Type} : List (Event Ambient X) → List (Event Ambient X)
 | [] => []
 | .marker _ :: tail => erase tail
 | e :: tail => e :: erase tail
/-- Exactly the deployed None-observer parent prefix: parse then common. -/
theorem success {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (v : transport.Variant)
 (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash) :
 erase (NMN_OracleFold.run H s (.ok (.Ok v)) common).2 =
 [.parse s (.ok (.Ok v)),.commonEnter s] := rfl
/-- A rejected parser never emits the profiling hook or a common event. -/
theorem rejection {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (e : verifier.Error)
 (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash) :
 erase (NMN_OracleFold.run H s (.ok (.Err e)) common).2 = [.parse s (.ok (.Err e))] := rfl
#print marker
#print success
#print rejection
#print axioms marker
#print axioms success
#print axioms rejection
end NMN_Observer
