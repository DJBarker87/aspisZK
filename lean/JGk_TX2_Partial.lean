import JGk_TX2_NativeRoots
import JGk_TX2_CountSource
import JGk_TX2_Padding0
import JGk_TX2_Padding1
import JGk_TX2_Padding2
import JFn_Resume
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_Partial
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep

/-- Fixed-input local consistency only. This contains no accepted slot, verifier,
batch, finish, wrapper, extracted pair or deployed security conclusion. -/
def LocalFacts : Prop :=
  JGf_TX2_M0Roots.InputLaw JGk_TX2_LeafBinding.actualInput0 ∧
  JGh_TX2_M1Roots.InputLaw JGk_TX2_LeafBinding.actualInput1 ∧
  JGf_TX2_M0Roots.SiblingLaw JGk_TX2_SiblingBase.native0 ∧
  JGh_TX2_M1Roots.SiblingLaw JGk_TX2_SiblingBase.native1 ∧
  JGc_TX2_M2Roots.SiblingLaw JGk_TX2_SiblingBase.native2 ∧
  OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGf_TX2_M0Roots.indices JGk_TX2_LeafBinding.actualInput0
      JGk_TX2_SiblingBase.native0 18 0)=JGf_TX2_M0Root.retainedRoot ∧
  OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGh_TX2_M1Roots.indices JGk_TX2_LeafBinding.actualInput1
      JGk_TX2_SiblingBase.native1 18 0)=JGh_TX2_M1Root.retainedRoot ∧
  (∀ s, Port4B_Install.leaves.op11 .Two (JGk_TX2_CountSource.front0 s)=ok (some 163#usize)) ∧
  (∀ s, Port4B_Install.leaves.op11 .Two (JGk_TX2_CountSource.front1 s)=ok (some 163#usize)) ∧
  (∀ s, Port4B_Install.leaves.op11 .Two (JGk_TX2_CountSource.front2 s)=ok (some 141#usize)) ∧
  JGk_TX2_Padding0.padding=List.replicate 288 0#u8 ∧
  JGk_TX2_Padding1.padding=List.replicate 288 0#u8 ∧
  JGk_TX2_Padding2.padding=List.replicate 288 0#u8

theorem local_nonvacuity : LocalFacts :=
  ⟨JGk_TX2_LeafBinding.inputs0,JGk_TX2_LeafBinding.inputs1,
    JGk_TX2_SiblingLaws.source0,JGk_TX2_SiblingLaws.source1,JGk_TX2_SiblingLaws.source2,
    JGk_TX2_NativeRoots.source0,JGk_TX2_NativeRoots.source1,
    JGk_TX2_CountSource.source0,JGk_TX2_CountSource.source1,JGk_TX2_CountSource.source2,
    JGk_TX2_Padding0.source,JGk_TX2_Padding1.source,JGk_TX2_Padding2.source⟩
#print axioms local_nonvacuity

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧ LocalFacts :=
  ⟨JFn_Resume.on_saved saved same JFp_SHADigest.digest D hash realizes,local_nonvacuity⟩
#print axioms on_saved
end AspisR1.JGk_TX2_Partial
end
