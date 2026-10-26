import F3T_HeadCanonical
import F3T_JoinBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Boundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

/-- Canonical byte boundary, retaining the exact collision alternative.
The native-pair production of joined/head remains a separate obligation. -/
theorem installed {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (H : Bytes → State) (s : Submission) (i : F3_Model.Input) (collision : Prop)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (joined : collision ∨ ((eval H (F3T_Installed.source c hashv (input c s))).1=
      (eval H (F3_Model.verifier D i)).1 ∧ (eval H (F3_Model.verifier D i)).2=true))
    (physical : i.physical=(input c s).physical) (stored : i.stored=s.stored)
    (root : State)
    (head : (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
      some (PublicInitFrame.frame (input c s).semantic.value.pubBytes root,
        H (PublicInitFrame.frame (input c s).semantic.value.pubBytes root))) :
    eval H (F3T_Installed.source c hashv (input c s))=
      eval H (F3_Model.verifier D (input c s)) ∨ collision := by
  exact (F3T_HeadCanonical.collision_or_source_eval c D H i s _ collision accepted joined
    physical stored root head).symm

#print axioms installed
end AspisR1.F3U_Boundary
end
