import NLW_064Reference
set_option autoImplicit false
noncomputable section
namespace NLW_064Common
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLW_064Invocation NLW_064Reference
/-- Every full 065 clause is installed at SAME arguments. 57607 comes from
CLOSED parser success, not a free bound or a parent-success hypothesis. -/
theorem install (H : Bytes → State) (bridge : ChildBridge H) (a : Args)
 (publicBound : a.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds a.checkpoint a.proof)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse a.proof=.ok (.Ok v))
 (result : Result Reply) (records : Records H)
 (child : NLT_NativeInvocation.Invocation H (NLT_RuntimeDigest.digest H) ()
  (childCode H a) result records) : CommonFacts H a result records := by
 have size := (NLE_ParseInstall.success a.proof v parsed).2
 have packet := bridge a.publicBytes a.proof a.checkpoint size publicBound
  ((NLW_RowSpec_065.root0_same _ _).mp root0)
 exact packet.1 result records child
#print install
#print axioms install
end NLW_064Common
