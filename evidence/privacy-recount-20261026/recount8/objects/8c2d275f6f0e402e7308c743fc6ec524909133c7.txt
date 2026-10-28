import R1Z.PV_RunJoin_MergeStep35
import R1Z.PV_RunJoin_MergeFold35
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeLoop35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_MergeFold35
variable [ExternalTypes]

theorem increment (i : Usize) (small : i.val<14336) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have hsize : 2^32≤UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  omega

/-- Entire actual sequential merge on a canonical successful evaluation
array. The worker evaluation law is separate; no semantic oracle is assumed
by name. Output values equal the independently specified ordered fold. -/
theorem complete (ops : ExternalFuns) (n : Nat) (count a i : Usize)
    (p es : Nat → Q) (bound : i.val+n=count.val) (small : count.val≤14336)
    (positive : a.val≠0) (samples : ∀ j, j<count.val → j/a.val<28)
    (hp : ∀ k, k<28 → canonical (p k)) (he : ∀ j, j<count.val → canonical (es j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.merge_evaluations_loop _ (ProverRwDictionaryTower.selected ops)
        (Array.to_slice (ProverCommitArray49.array count (fun j => core.result.Result.Ok (es j))))
        a (array p) count i = .ok (array out,none) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      (fun k => value (out k))=fold n (fun k => value (p k)) (fun j => value (es j)) a.val i.val := by
  induction n generalizing p i with
  | zero =>
    refine ⟨p,?_,hp,rfl⟩
    have hi : ¬i<count := by change ¬i.val<count.val;omega
    unfold host_sumcheck.merge_evaluations_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_MergeStep35.stop ops _ _ _ _ _ hi,bind_tc_ok]
  | succ n ih =>
    have hi : i.val<count.val := by omega
    have inc := increment i (by omega)
    obtain ⟨s,q,hs,hq,hd,step⟩ := PV_RunJoin_MergeStep35.success ops _ a count i p
      (by exact hi) positive (samples _ hi) (es i.val)
      (slice_values count (fun j => core.result.Result.Ok (es j)) i hi) hp (he _ hi)
    obtain ⟨out,hout,hc,hm⟩ := ih (Usize.wrapping_add i 1#usize)
      (Function.update p s.val q) (by rw [inc];omega) (canonical_update p s.val q hp hq)
    refine ⟨out,?_,hc,?_⟩
    · unfold host_sumcheck.merge_evaluations_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [step]
      simp only [bind_tc_ok]
      exact hout
    · rw [hm,fold,map_update,hd,hs,inc]

#print axioms increment
#print axioms complete
end R1Z.PV_RunJoin_MergeLoop35
