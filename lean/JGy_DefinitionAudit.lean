import JGy_LightCore
import JGh_TX2_NodeViews
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_DefinitionAudit
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem dictionary {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) :
    JGy_G_JGc_TX2_RealLeaves.dictionary D=JGc_TX2_RealLeaves.dictionary D := rfl

theorem parentIndex (i : U32) :
    JGy_G_JGk_TX2_ParentWrite.parentIndex i=JGk_TX2_ParentWrite.parentIndex i := rfl

theorem after (s : reference.Scratch) (index : U32) (w : Usize)
    (value : Array U8 32#usize) (cursor : Usize) :
    JGy_G_JGk_TX2_ParentWrite.after s index w value cursor=
      JGk_TX2_ParentWrite.after s index w value cursor := rfl

theorem readCell (nodes : Slice U8) (cursor : Nat) :
    JGy_G_JGh_TX2_NodeViews.readCell nodes cursor=JGh_TX2_NodeViews.readCell nodes cursor := by
  unfold JGy_G_JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.readCell
  rfl

#print axioms dictionary
#print axioms parentIndex
#print axioms after
#print axioms readCell
end AspisR1.JGy_DefinitionAudit
end
