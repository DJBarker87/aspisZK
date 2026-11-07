import NMD_CutState
set_option autoImplicit false
noncomputable section
namespace NMD_SegmentFold
open Aeneas Aeneas.Std VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NMD_CutState
/-- Segments produce only chronological boundaries. Common's entire Native
packet, including independent allocation-stop prefixes, is retained. -/
inductive Segments {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical) : End H s.frame.args → List (Event Ambient X) → Prop where
 | fail (e : Aeneas.Std.Error) (parsed : NLE_ParseInstall.parse s.frame.args.proof=.fail e) :
   Segments H s (.parseFail e) [.parse s.frame (.fail e)]
 | div (parsed : NLE_ParseInstall.parse s.frame.args.proof=.div) :
   Segments H s .parseDiv [.parse s.frame .div]
 | reject (e : verifier.Error) (parsed : NLE_ParseInstall.parse s.frame.args.proof=.ok (.Err e)) :
   Segments H s (.parseReject e) [.parse s.frame (.ok (.Err e))]
 | common (v : transport.Variant) (parsed : NLE_ParseInstall.parse s.frame.args.proof=.ok (.Ok v))
   (outcome : NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash)
   (child : NLT_CompleteRoot.Native H s.frame.args.digest s.frame.args.publicBytes
    s.frame.args.proof s.frame.args.checkpoint s.frame.args.hash outcome) :
   Segments H s (.common outcome) [.parse s.frame (.ok (.Ok v)),.marker s.frame,.commonEnter s.frame]
/-- Equality to NLW's complete-outcome cut relation, not an admission of its
physical producer. The additional Physical carrier is not erased by a root. -/
theorem transcription {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical) (outcome : End H s.frame.args)
 (events : List (Event Ambient X)) :
 Segments H s outcome events ↔ Invocation H s.frame outcome events := by
 constructor
 · intro h
   cases h with
   | fail e p => exact .fail e p
   | div p => exact .div p
   | reject e p => exact .reject e p
   | common v p o c => exact .common v p o c
 · intro h
   cases h with
   | fail e p => exact .fail e p
   | div p => exact .div p
   | reject e p => exact .reject e p
   | common v p o c => exact .common v p o c
/-- RowSpec-parameterized fold while the native producer is unestablished. -/
theorem fold {Ambient X Physical : Type} (H : Bytes → State)
 (bridge : ChildBridge H) (s : Parent Ambient X Physical)
 (publicBound : s.frame.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.frame.args.checkpoint s.frame.args.proof)
 (outcome : End H s.frame.args) (events : List (Event Ambient X))
 (segments : Segments H s outcome events) :
 Law H s.frame.args outcome ∧ events=chronology H s.frame outcome :=
 NLW_Full064.fold H bridge s.frame publicBound root0 outcome events
  ((transcription H s outcome events).mp segments)
#print axioms transcription
#print axioms fold
end NMD_SegmentFold
