import R1Z.PV_RunJoin_AccStep38
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AccLoop38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- Every source coefficient is updated once, in ascending order. The
remaining suffix is traversed symbolically, including every array restoration. -/
theorem complete (ops : ExternalFuns) (n : Nat) (k : Usize)
    (p : Nat → Q) (basis : Nat → U32) (scale : Q) (bound : k.val+n=28)
    (hp : ∀ j, j<28 → canonical (p j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolation_accumulate_loop _ (ProverRwP6BodyCandidate.selected ops)
        (array p) (ProverCommitArray49.array 28#usize basis) scale k = .ok (array out) ∧
      (∀ j, j<28 → canonical (out j)) ∧
      ∀ j, j<28 → value (out j)=
        if k.val≤j ∧ j<k.val+n then value (p j)+value scale*ProverCommitScalar48.embed (basis j)
        else value (p j) := by
  induction n generalizing k p with
  | zero =>
    refine ⟨p,?_,hp,?_⟩
    · unfold host_sumcheck.interpolation_accumulate_loop
      rw [ProverRw19LoopBind.loop_bind]
      simp only [PV_RunJoin_AccStep38.stop ops _ _ scale k (by omega),bind_tc_ok]
    · intro j hj
      rw [if_neg (by omega)]
  | succ n ih =>
    have hk : k.val<28 := by omega
    have inc := PV_RunJoin_MergeLoop35.increment k (by omega)
    obtain ⟨z,hstep,hcz,hvz⟩ := PV_RunJoin_AccStep38.step ops p basis scale k hk hp
    obtain ⟨out,hout,hcan,hval⟩ := ih (Usize.wrapping_add k 1#usize)
      (Function.update p k.val z) (by rw [inc];omega)
      (PV_RunJoin_MergeFold35.canonical_update p k.val z hp hcz)
    refine ⟨out,?_,hcan,?_⟩
    · unfold host_sumcheck.interpolation_accumulate_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hstep]
      simp only [bind_tc_ok]
      exact hout
    · intro j hj
      rw [hval j hj,inc]
      by_cases eq : j=k.val
      · subst j
        rw [if_neg (by omega),Function.update_self,if_pos (by omega)]
        exact hvz
      · simp only [Function.update_of_ne eq]
        have tests : (k.val+1≤j ∧ j<k.val+1+n) = (k.val≤j ∧ j<k.val+(n+1)) :=
          propext (by omega)
        simp only [tests]

#print axioms complete
end R1Z.PV_RunJoin_AccLoop38
