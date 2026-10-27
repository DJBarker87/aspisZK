import F3T_InitHead
import F3T_InitialConstructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_SemanticHead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem bytes (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2=true)
    (encoded : Bytes) (root : State)
    (head : (eval H (F3_Model.verifier D i)).1.head?=
      some (PublicInitFrame.frame encoded root,H (PublicInitFrame.frame encoded root))) :
    i.semantic.value.pubBytes=encoded := by
  obtain ⟨r,w,initial⟩ := F3T_InitialConstructor.initial D H i accepted
  have model := F3T_InitHead.head D i r w initial H
  have pair := Option.some.inj (model.symm.trans head)
  exact F3T_InitFrame.public_bytes _ _ _ _ (congrArg Prod.fst pair)

#print axioms bytes
end AspisR1.F3T_SemanticHead
end
