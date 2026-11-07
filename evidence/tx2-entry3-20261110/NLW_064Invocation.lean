import NLW_RowSpec_065
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLW_064Invocation
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Reply := core.result.Result Unit verifier.Error
abbrev Records (H : Bytes → State) :=
 List (NLT_NativeInvocation.Occurrence H (NLT_RuntimeDigest.digest H) ())
structure Args where
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
/-- Original decoded value carriers plus the entire protected caller frame,
including SDK cells/tokens and unrelated memory. Parent064 creates no loans
or owned buffers. Child-local allocations stay in its complete cut records. -/
structure Frame (Ambient : Type) where
 args : Args
 world : NLM_PacketTypes.World Ambient
inductive Event (Ambient : Type) (H : Bytes → State) where
 | parse (before : Frame Ambient)
   (reply : Result (core.result.Result transport.Variant verifier.Error))
 | marker (before : Frame Ambient)
 | common (before : Frame Ambient) (reply : Result Reply) (records : Records H)
def childCode (H : Bytes → State) (a : Args) :=
 NLT_NativeSource.skeleton H (NLT_RuntimeDigest.digest H)
  a.publicBytes a.proof a.checkpoint ()
/-- Reviewed source-ordered native cut interpretation. Local ?/marker/tail
transcriptions use the pinned empty-modifies segment contracts. Common is
ONE complete nested invocation, not an independently chosen endpoint/log.
Physical encoding of Frame is still a review item, not a new runtime axiom. -/
inductive Invocation {Ambient : Type} (H : Bytes → State) (s : Frame Ambient) :
 Result Reply → Records H → List (Event Ambient H) → Prop where
 | fail (e : Aeneas.Std.Error)
   (parsed : NLE_ParseInstall.parse s.args.proof=.fail e) :
   Invocation H s (.fail e) [] [.parse s (.fail e)]
 | div (parsed : NLE_ParseInstall.parse s.args.proof=.div) :
   Invocation H s .div [] [.parse s .div]
 | reject (e : verifier.Error)
   (parsed : NLE_ParseInstall.parse s.args.proof=.ok (.Err e)) :
   Invocation H s (.ok (.Err e)) [] [.parse s (.ok (.Err e))]
 | common (v : transport.Variant)
   (parsed : NLE_ParseInstall.parse s.args.proof=.ok (.Ok v))
   (result : Result Reply) (records : Records H)
   (child : NLT_NativeInvocation.Invocation H (NLT_RuntimeDigest.digest H) ()
    (childCode H s.args) result records) :
   Invocation H s result records
    [.parse s (.ok (.Ok v)),.marker s,.common s result records]
/-- Resolved-only pre-NLT-F1 child projection. It may be a
parameter in this RESTRICTED support fold; it is not the full child packet. -/
def ChildBridge (H : Bytes → State) : Prop :=
 ∀ (pub proof ck : Slice U8), proof.val.length=57607 → pub.val.length≤1880 →
 NLP_InputDomain.Root0 ck proof → NLW_RowSpec_065.ResolvedProjectionSpec H pub proof ck
#print Invocation
#print ChildBridge
end NLW_064Invocation
