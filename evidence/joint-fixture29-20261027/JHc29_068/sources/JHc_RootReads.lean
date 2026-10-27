import JHc_Tree2Part2
import JHc_Tree0Part2
import JHc_Tree1Part2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_RootReads
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem root0 : Array.index_usize JFo_Prepared.value.roots 0#usize=
    ok (encodeState JHc_Gr_M0Root.retainedRoot) := by
  change ok JFq_Root0.value=_
  exact congrArg ok (Subtype.ext JGf_TX2_M0Root.selected_root).symm
#print axioms root0

theorem root1 : Array.index_usize JFo_Prepared.value.roots 1#usize=
    ok (encodeState JHc_Gr_M1Root.retainedRoot) := by
  change ok JFq_Root1.value=_
  exact congrArg ok (Subtype.ext JGh_TX2_M1Root.selected_root).symm
#print axioms root1

theorem folded : JGe_View.folded=encodeState JHc_Gr_M2Root.retainedRoot := by
  apply Subtype.ext
  exact JGc_TX2_M2Root.selected_root.trans JGc_TX2_M2Root.encoded_root.symm
#print axioms folded
end AspisR1.JHc_RootReads
end
