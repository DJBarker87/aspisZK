import JGk_TX2_LeafBinding
import JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_NativeRoots
open AspisV8R19.SourceDuplexStep

theorem source0 : OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGf_TX2_M0Roots.indices JGk_TX2_LeafBinding.actualInput0
      JGk_TX2_SiblingBase.native0 18 0)=JGf_TX2_M0Root.retainedRoot :=
  JGf_TX2_M0Root.source _ _ JGk_TX2_LeafBinding.inputs0 JGk_TX2_SiblingLaws.source0
#print axioms source0

theorem source1 : OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGh_TX2_M1Roots.indices JGk_TX2_LeafBinding.actualInput1
      JGk_TX2_SiblingBase.native1 18 0)=JGh_TX2_M1Root.retainedRoot :=
  JGh_TX2_M1Root.source _ _ JGk_TX2_LeafBinding.inputs1 JGk_TX2_SiblingLaws.source1
#print axioms source1

end AspisR1.JGk_TX2_NativeRoots
end
