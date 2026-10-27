import F3U_Boundary
set_option autoImplicit false
namespace AspisR1.F3U_SubmissionIdentity
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

theorem ext (s t : Submission) (pub : s.publicBytes=t.publicBytes) (proof : s.stored=t.stored) : s=t := by
  cases s
  cases t
  cases pub
  cases proof
  rfl

theorem transport {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (H : Bytes → State) (s t : Submission) (collision : Prop)
    (pub : s.publicBytes=t.publicBytes) (proof : s.stored=t.stored)
    (joined : eval H (F3T_Installed.source c hashv (input c s))=
      eval H (F3_Model.verifier D (input c s)) ∨ collision) :
    eval H (F3T_Installed.source c hashv (input c t))=
      eval H (F3_Model.verifier D (input c t)) ∨ collision := by
  rw [ext s t pub proof] at joined
  exact joined

#print axioms ext
#print axioms transport
end AspisR1.F3U_SubmissionIdentity
