import R1Z.PV_RunJoin_InterpolationRow38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InterpolationLoop38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_AccPolynomial38
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (values : Nat → Q) (n : Nat)
    (i : Usize) (p : Nat → Q) (bound : i.val+n=28)
    (hp : ∀ k, k<28 → canonical (p k)) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolate_loop _ (ProverRwP6BodyCandidate.selected ops)
        (array values) (array p) i = .ok (array out) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      poly out=poly p+ProverCommitInterpolationOutput48.rowSum (fun k => old (values k)) i.val n := by
  induction n generalizing i p with
  | zero =>
    refine ⟨p,?_,hp,?_⟩
    · unfold host_sumcheck.interpolate_loop
      rw [ProverRw19LoopBind.loop_bind]
      simp only [PV_RunJoin_InterpolationRow38.stop ops _ _ i (by omega),bind_tc_ok]
    · rw [ProverCommitInterpolationOutput48.rowSum,add_zero]
  | succ n ih =>
    have hi : i.val<28 := by omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨next,hnext,hcnext,hdnext⟩ := PV_RunJoin_InterpolationRow38.step ops values p i hi hp
    obtain ⟨out,hout,hcan,hpoly⟩ := ih (Usize.wrapping_add i 1#usize) next (by rw [inc];omega) hcnext
    refine ⟨out,?_,hcan,?_⟩
    · unfold host_sumcheck.interpolate_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hnext]
      simp only [bind_tc_ok]
      exact hout
    · rw [hpoly,hdnext,inc,ProverCommitInterpolationOutput48.rowSum]
      exact add_assoc _ _ _

#print axioms complete
end R1Z.PV_RunJoin_InterpolationLoop38
