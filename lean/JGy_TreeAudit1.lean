import JGy_Tree1Part7
import JGw_Tree1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_TreeAudit1
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem root : JGy_Gr_M1Root.retainedRoot=JGr_M1Root.retainedRoot := rfl

theorem output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) :
    JGy_Gu_Verify1.output D hash s=JGu_Verify1.output D hash s := rfl

/-- The full native adapter proposition is unchanged, including chosen output. -/
theorem statement : @JGy_Gw_Tree1.tree=@JGw_Tree1.tree := rfl

#print axioms root
#print axioms output
#print axioms statement
end AspisR1.JGy_TreeAudit1
end
