import F3T_SemanticHead
import F3T_PublicExt
import F3T_ByteTag
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_HeadCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

theorem program {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input) (s : Submission)
    (accepted : (eval H (F3_Model.verifier D i)).2=true)
    (physical : i.physical=(input c s).physical) (stored : i.stored=s.stored)
    (root : State)
    (head : (eval H (F3_Model.verifier D i)).1.head?=
      some (PublicInitFrame.frame (input c s).semantic.value.pubBytes root,
        H (PublicInitFrame.frame (input c s).semantic.value.pubBytes root))) :
    F3_Model.verifier D i=F3_Model.verifier D (input c s) := by
  have sem : i.semantic=(input c s).semantic := F3T_PublicExt.semantic_ext _ _
    (F3T_SemanticHead.bytes D H i accepted _ root head)
    ((F3T_AcceptedParser.tag D H i accepted).trans (F3T_ByteTag.semantic_tag c s).symm)
  rw [F3T_AcceptedReplacement.program D H i accepted]
  apply F3T_PrefixCongr.verifier_congr D (F3T_AcceptedReplacement.replace i) (input c s) sem physical stored
  intro row below
  change LiteralTranscript.erase (Port1_StoredCarrier.proof i.stored row)=
    LiteralTranscript.erase (Port1_StoredCarrier.proof s.stored row)
  rw [stored]

theorem source_eval {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input) (s : Submission)
    (source : AspisV8R19.MemoizedProgramLaw.Program Bytes State Bool)
    (sourceAccepted : (eval H source).2=true)
    (accepted : (eval H (F3_Model.verifier D i)).2=true)
    (logs : (eval H source).1=(eval H (F3_Model.verifier D i)).1)
    (physical : i.physical=(input c s).physical) (stored : i.stored=s.stored)
    (root : State)
    (head : (eval H source).1.head?=
      some (PublicInitFrame.frame (input c s).semantic.value.pubBytes root,
        H (PublicInitFrame.frame (input c s).semantic.value.pubBytes root))) :
    eval H source=eval H (F3_Model.verifier D (input c s)) := by
  have same : eval H source=eval H (F3_Model.verifier D i) :=
    Prod.ext logs (sourceAccepted.trans accepted.symm)
  rw [program c D H i s accepted physical stored root (by rw [← logs];exact head)] at same
  exact same

#print axioms source_eval
#print axioms program
end AspisR1.F3T_HeadCanonical
end
