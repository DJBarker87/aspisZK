import JGf_TX2_M0Root
import JGc_TX2_Partial
import JGc_TX2_RealLeaves
import JGc_TX2_QueryFixture
import JGc_TX2_M2Root
import JGc_TX2_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_Partial
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest)
    (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    (Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JGc_TX2_QueryFixture.Calls err geometrySeed querySeed ∧
    JGc_TX2_RealLeaves.Calls (VTop_Checkpoint.digest D) hash ∧
    ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
      JGc_TX2_M2Roots.InputLaw f ∧ JGc_TX2_M2Roots.SiblingLaw g ∧
      OracleDecisionMultiTree.root JFp_SHADigest.digest
        (OracleDecisionMultiBuild.build JGc_TX2_M2Roots.indices f g 18 0)=JGc_TX2_M2Root.retainedRoot) ∧
    (∃ (f : Nat → Bytes) (g : Nat → Nat → State),
      JGf_TX2_M0Roots.InputLaw f ∧ JGf_TX2_M0Roots.SiblingLaw g ∧
      OracleDecisionMultiTree.root JFp_SHADigest.digest
        (OracleDecisionMultiBuild.build JGf_TX2_M0Roots.indices f g 18 0)=JGf_TX2_M0Root.retainedRoot) := by
  exact ⟨JGc_TX2_Partial.on_saved saved same D hash realizes querySeed err geometrySeed,
    JGf_TX2_M0Root.inhabited⟩
#print axioms on_saved
#check @on_saved
end AspisR1.JGf_TX2_Partial
end
