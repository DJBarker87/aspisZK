import NNR_OuterInvert
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_OuterBuild
open Aeneas Aeneas.Std Result VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Explicitly pin both the oracle and frame at the native constructor. -/
theorem accepted {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (v : transport.Variant) (parser : NMN_064.ParserNative s.args.proof (.ok (.Ok v)))
 (records : List (NLT_NativeInvocation.Occurrence H s.args.digest s.args.hash))
 (native : NLT_CompleteRoot.Native H s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint
  s.args.hash (.resolved (.ok (.Ok ())) records)) :
 ∃ events, NMN_064.Native H s (.common (.resolved (.ok (.Ok ())) records)) events := by
 refine ⟨[.parse s (.ok (.Ok v)),.marker s,.commonEnter s],?_⟩
 exact @NMN_064.Native.observed Ambient X H s (.ok (.Ok v))
  (fun _ => .resolved (.ok (.Ok ())) records) parser (fun _ _ => native)
#print axioms accepted
end AspisR1.NNR_OuterBuild
end
