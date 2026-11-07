import NLW_Full064Law
set_option autoImplicit false
noncomputable section
namespace NLW_Full064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Complete-outcome parameterized fold,not a row root. Full child packet is
consumed at original arguments; proof57607 is derived at that SAME parser
branch. Public1880 and BOTH-root provenance still need caller installation. -/
theorem fold {Ambient X : Type} (H : Bytes → State) (bridge : ChildBridge H)
 (s : Frame Ambient X) (publicBound : s.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.args.checkpoint s.args.proof)
 (outcome : End H s.args) (events : List (Event Ambient X))
 (native : Invocation H s outcome events) :
 Law H s.args outcome ∧ events=chronology H s outcome := by
 cases native with
 | fail e parsed => exact ⟨parsed,by simp [chronology,parsed]⟩
 | div parsed => exact ⟨parsed,by simp [chronology,parsed]⟩
 | reject e parsed => exact ⟨parsed,by simp [chronology,parsed]⟩
 | common v parsed outcome child =>
   have packet:=bridge s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint s.args.hash
    (NLE_ParseInstall.success s.args.proof v parsed).2 publicBound
    ((NLW_RowSpec_065.root0_same _ _).mp root0)
   exact ⟨packet.1 outcome child,by simp [chronology,parsed]⟩
theorem no_invalid (H : Bytes → State) (bridge : ChildBridge H) {X : Type}
 (a : Args X) (publicBound : a.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds a.checkpoint a.proof) (v : transport.Variant)
 (parsed : NLE_ParseInstall.parse a.proof=.ok (.Ok v))
 (records : List (NLT_NativeInvocation.Occurrence H a.digest a.hash)) :
 ¬NLT_NativeInvocation.Invalid H a.digest a.hash
 (NLT_NativeSource.skeleton H a.digest a.publicBytes a.proof a.checkpoint a.hash) records := by
 have packet:=bridge a.digest a.publicBytes a.proof a.checkpoint a.hash
  (NLE_ParseInstall.success a.proof v parsed).2 publicBound
  ((NLW_RowSpec_065.root0_same _ _).mp root0)
 exact packet.2 records
set_option pp.proofs false
#print fold
#print no_invalid
#print ChildBridge
#print Invocation
#print NLT_CompleteRoot.RowSpec
#print NLT_CompleteRoot.StoppedLaw
#print axioms fold
#print axioms no_invalid
end NLW_Full064
