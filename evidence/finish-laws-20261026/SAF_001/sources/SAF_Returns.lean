import RowFinish_Control
import Port3_FinishControl

set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_Returns
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open RowFinish_Control
variable {W : Type}

/-- Actual successful round returns, obtained by inverting the installed body. -/
theorem round (ops : FinishOps W) (bytes : Slice U8) (alpha claim out : E)
    (r : Usize)
    (success : verifier.finishRelationRoundWithOps (Port3_FinishStage.release ops)
      bytes alpha claim r = ok (.Ok out)) :
    ∃ values : RoundValues ops bytes alpha claim, values.value = out := by
  obtain ⟨c0,c4,lhs,quarter,rhs,h0,h4,ha,hq,hm,_,he⟩ :=
    Port3_FinishControl.round_success (Port3_FinishStage.release ops) bytes alpha claim out r success
  exact ⟨⟨c0,c4,lhs,quarter,rhs,out,h0,h4,ha,hq,hm,he⟩,rfl⟩

/-- The installed successful S2 finish supplies all fifteen primitive-return
families. No independently selected execution or arithmetic law is an input. -/
theorem finish (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (s2 : p.variant = .S2)
    (success : Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) :
    ∃ (alpha0 alpha1 : E)
      (r0 : RoundValues ops v.round0 alpha0 p.claim)
      (r1 : RoundValues ops v.round1 alpha1 r0.value)
      (weights : W) (alphas : Slice E) (pair dot : E),
      Array.index_usize p.alpha 0#usize = ok alpha0 ∧
      Array.index_usize p.alpha 1#usize = ok alpha1 ∧
      ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas ∧
      ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair) ∧
      ops.dot v.final_message a.weights.deref = ok (.Ok dot) ∧
      r0.lhs = r0.rhs ∧ r1.lhs = r1.rhs ∧ pair = r1.value ∧ dot = a.rhs := by
  have native := (Port3_QueryInstall.success_iff _ _).mp success
  rw [Port4D_Round.parent_eq] at native
  have two : (Port3_FinishStage.release ops).folds p.variant = ok 2#usize := by
    rw [s2]; rfl
  obtain ⟨alpha0,value0,alpha1,value1,weights,alphas,pair,dot,
    h0,hr0,h1,hr1,hw,hs,hp,hep,hd,_,hed⟩ :=
    Port3_FinishControl.finish_success (Port3_FinishStage.release ops) v p a none two native
  obtain ⟨r0,ev0⟩ := round ops v.round0 alpha0 p.claim value0 0#usize hr0
  obtain ⟨r1,ev1⟩ := round ops v.round1 alpha1 r0.value value1 1#usize (ev0 ▸ hr1)
  have eq0 : r0.lhs = r0.rhs := by
    have value := RowFinish_Control.round_value ops v.round0 alpha0 p.claim 0#usize r0
    rw [Port4D_Round.round_zero] at value
    rw [hr0] at value
    split at value
    · assumption
    · cases value
  have eq1 : r1.lhs = r1.rhs := by
    have value := RowFinish_Control.round_value ops v.round1 alpha1 r0.value 1#usize r1
    rw [Port4D_Round.round_one] at value
    rw [ev0,hr1] at value
    split at value
    · assumption
    · cases value
  exact ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,h0,h1,hw,hs,hp,hd,
    eq0,eq1,(Port3_FinishStage.ne_false pair value1 hep).trans ev1.symm,
    Port3_FinishStage.ne_false dot a.rhs hed⟩

#print axioms round
#print axioms finish
end AspisR1.SAF_Returns
end
