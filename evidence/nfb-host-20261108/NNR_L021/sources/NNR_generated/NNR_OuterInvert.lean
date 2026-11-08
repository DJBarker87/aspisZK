import NNR_C04Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_OuterInvert
open Aeneas Aeneas.Std Result VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem accepted {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (records : List (NLT_NativeInvocation.Occurrence H s.args.digest s.args.hash))
 (events : List (Event Ambient X))
 (native : NMN_064.Native H s (.common (.resolved (.ok (.Ok ())) records)) events) :
 ∃ v, NMN_064.ParserNative s.args.proof (.ok (.Ok v)) ∧
 NLT_CompleteRoot.Native H s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint
  s.args.hash (.resolved (.ok (.Ok ())) records) := by
 have invert : ∀ outcome events, NMN_064.Native H s outcome events →
   ∀ rs, outcome = .common (.resolved (.ok (.Ok ())) rs) →
   ∃ v, NMN_064.ParserNative s.args.proof (.ok (.Ok v)) ∧
    NLT_CompleteRoot.Native H s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint
     s.args.hash (.resolved (.ok (.Ok ())) rs) := by
  intro outcome ev hn
  cases hn with
  | observed parsed common parser child =>
   intro rs equal
   cases parsed with
   | fail error => cases equal
   | div => cases equal
   | ok reply =>
    cases reply with
    | Err error => cases equal
    | Ok v =>
     have eq : common v = .resolved (.ok (.Ok ())) rs := End.common.inj equal
     have h := child v rfl
     rw [eq] at h
     exact ⟨v,parser,h⟩
 exact invert _ _ native records rfl
#print axioms accepted
end AspisR1.NNR_OuterInvert
end
