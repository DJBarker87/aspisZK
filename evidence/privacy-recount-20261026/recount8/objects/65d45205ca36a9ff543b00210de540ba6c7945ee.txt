import R1Z.PV_RunJoin_GammaPowers44
import R1Z.PV_RunJoin_GammaVector44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaAssociation44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_BatchRowValue44 (table array)
variable [ExternalTypes]

theorem powers (ops : ExternalFuns) (g : Raw) (hg : canonical g) :
    ∃ p : Nat → Raw, AspisR1ProducerRelease47.gamma (source g) = .ok (sourceArray 29#usize p) ∧
      (PV_RunJoin_GammaPowers44.dict ops).op254 29#usize (current (source g)) = .ok (array 29#usize p) ∧
      (∀ i, i < 29 → canonical (p i)) ∧ ∀ i, i < 29 → value (p i) = value g ^ i := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitGamma48.gamma_exact g hg
  obtain ⟨p',hp',hcp',hdp'⟩ := PV_RunJoin_GammaPowers44.gamma ops g hg
  have same : array 29#usize p' = array 29#usize p := by
    apply Subtype.ext
    dsimp only [array,ProverCommitArray49.array]
    apply congrArg List.ofFn
    funext i
    have he : p' i.val = p i.val := PV_RunJoin_WideUnique44.unique _ _ (hcp' _ i.isLt) (hcp _ i.isLt)
      ((hdp' _ i.isLt).trans (hdp _ i.isLt).symm)
    rw [he]
  exact ⟨p,hp,hp'.trans (congrArg Result.ok same),hcp,hdp⟩

theorem complete (ops : ExternalFuns) (c : Nat → Nat → Raw) (g : Raw)
    (hc : ∀ l, l < 29 → ∀ j, j < 1024 → canonical (c l j)) (hg : canonical g) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.opening_batch _ (PV_RunJoin_GammaPowers44.dict ops) (table c) (current (source g)) = .ok out ∧
      ProverCommitGammaOutput53.run (ProverCommitGammaCell53.table c) (source g) = .ok (sourceArray 1024#usize z) ∧
      Array.to_slice (array 1024#usize z) = alloc.vec.Vec.deref out ∧
      (∀ j, j < 1024 → canonical (z j)) := by
  obtain ⟨p,hp,hcur,hcp,hdp⟩ := powers ops g hg
  obtain ⟨z,out,hout,hz,himage,hcz,hdz⟩ := PV_RunJoin_GammaVector44.complete
    (PV_RunJoin_GammaPowers44.inputs ops) c p hc hcp
  refine ⟨z,out,?_,?_,himage,hcz⟩
  · unfold prover.opening_batch
    simp only [weights.powers,hcur,bind_tc_ok]
    exact hout
  · simp only [ProverCommitGammaOutput53.run,hp,bind_tc_ok,hz]
#print axioms powers
#print axioms complete
end R1Z.PV_RunJoin_GammaAssociation44
