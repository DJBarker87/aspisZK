import SAG_DotAdapter
import CheckpointBytes5Output
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotDecode
open Aeneas Aeneas.Std
open AspisR1Stage2.Stage2Finish

theorem q_decode (q : K) : CheckpointBytes5Output.ofK q =
    AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (SAG_DotAdapter.toFinishQ q) := by
  ext <;> simp [CheckpointBytes5Output.ofK,CheckpointBytes5Output.limb,
    RetainedExactLimbCodec.qm31ExactLimbEquiv,RetainedExactLimbCodec.limbsToQM31Exact,
    RetainedExactLimbCodec.m31ResidueEquiv,
    SAG_DotAdapter.toFinishQ,
    AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded,
    AspisR1FinishDotReturnedProductWords.finishQMWords,
    AspisV8R17.QM31WordTower.decodeQ,AspisV8R17.QM31WordTower.decodeC,
    AspisV8R17.QM31WordTower.embedQ,AspisV8R17.QM31WordTower.embedC,
    AspisV8R17.QM31WordResidues.decodeQ,AspisV8R17.QM31WordResidues.decodeC,
    ZMod.finEquiv]
  all_goals apply Fin.ext; rfl

theorem e_decode (x : E) : CheckpointBytes5Output.ofE x = SAG_DotAdapter.decodeStage x := by
  rw [SAG_DotAdapter.decodeStage,AspisR1FinishDotReturnedDecodedValueV1.decodeFinish_eq_word_tower]
  change (⟨CheckpointBytes5Output.ofK x.c0,CheckpointBytes5Output.ofK x.c1⟩ : AspisWideTower.WideExact) = _
  rw [q_decode,q_decode]
  rfl

#print axioms q_decode
#print axioms e_decode
end AspisR1.SAG_DotDecode
end
