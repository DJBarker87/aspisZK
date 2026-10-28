import R1Z.PV_RunJoin_RoundAssociation44
import R1Z.ProverCommitRoundShape49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundSecond44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem pad_prefix (q : Nat → Raw) : array 256#usize (ProverCommitRoundShape49.pad q) = array 256#usize q := by
  apply Subtype.ext
  dsimp only [array,ProverCommitArray49.array]
  apply congrArg List.ofFn
  funext i
  have hi : i.val < 256 := i.isLt
  rw [ProverCommitRoundShape49.pad,if_pos hi]

theorem complete (ops : ExternalFuns) (q w : Nat → Raw)
    (hq : ∀ k, k < 256 → canonical (q k)) (hw : ∀ k, k < 256 → canonical (w k)) :
    ∃ ys : Nat → Raw,
      @prover.round _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array 256#usize q)) (Array.to_slice (array 256#usize w)) = .ok (array 7#usize ys) ∧
      ProverCommitRoundShape49.run (sourceArray 256#usize q) (sourceArray 256#usize w) =
        .ok (List.ofFn (fun k : Fin 7 => source (ys k.val))) ∧ (∀ k, k < 7 → canonical (ys k)) := by
  obtain ⟨ys,hy,hret,hcy⟩ := PV_RunJoin_RoundAssociation44.complete ops 256#usize (by decide)
    (ProverCommitRoundShape49.pad q) (ProverCommitRoundShape49.pad w)
    (ProverCommitRoundShape49.pad_canonical q hq) (ProverCommitRoundShape49.pad_canonical w hw)
  rw [pad_prefix q,pad_prefix w] at hy
  refine ⟨ys,hy,?_,hcy⟩
  simpa only [ProverCommitRoundShape49.run,ProverCommitRoundShape49.lift_source,show (256#usize).val / 4 = 64 from rfl] using hret
#print axioms pad_prefix
#print axioms complete
end R1Z.PV_RunJoin_RoundSecond44
