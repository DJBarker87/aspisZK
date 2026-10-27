import JGy_Tree0Part7
import JGw_Tree0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_TreeAudit0
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem root : JGy_Gr_M0Root.retainedRoot=JGr_M0Root.retainedRoot := rfl

theorem output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) :
    JGy_Gu_Verify0.output D hash s=JGu_Verify0.output D hash s := rfl

/-- The full native adapter proposition is unchanged, including chosen output. -/
theorem statement : @JGy_Gw_Tree0.tree=@JGw_Tree0.tree := rfl

#print axioms root
#print axioms output
#print axioms statement
end AspisR1.JGy_TreeAudit0
end
