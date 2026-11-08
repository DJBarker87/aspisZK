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
 cases native with
 | observed parsed common parser child =>
  cases parsed with
  | fail error => contradiction
  | div => contradiction
  | ok reply =>
   cases reply with
   | Err error => contradiction
   | Ok v => exact ⟨v,parser,child v rfl⟩
#print axioms accepted
end AspisR1.NNR_OuterInvert
end
