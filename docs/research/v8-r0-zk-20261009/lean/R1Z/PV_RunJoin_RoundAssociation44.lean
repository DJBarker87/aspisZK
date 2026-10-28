import R1Z.PV_RunJoin_RoundResult44
import R1Z.PV_RunJoin_ArrayUnique44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundAssociation44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (small : count.val / 4 ≤ 256)
    (q w : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (hw : ∀ k, k < 1024 → canonical (w k)) :
    ∃ ys : Nat → Raw,
      @prover.round _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) = .ok (array 7#usize ys) ∧
      ProverCommitRoundScaled48.run (count.val / 4) (sourceArray 1024#usize q) (sourceArray 1024#usize w) =
        .ok (List.ofFn (fun k : Fin 7 => source (ys k.val))) ∧
      (∀ k, k < 7 → canonical (ys k)) := by
  obtain ⟨ys,hy,hcy,hdy⟩ := ProverCommitRoundScaled48.scaled_output (count.val / 4) small q w hq hw
  obtain ⟨xs,hx,hcx,hdx⟩ := PV_RunJoin_RoundResult44.complete ops count small q w hq hw
  have same : array 7#usize xs = array 7#usize ys := PV_RunJoin_ArrayUnique44.pointwise 7#usize xs ys
    hcx hcy (fun k hk => (hdx k hk).trans (hdy k hk).symm)
  exact ⟨ys,hx.trans (congrArg Result.ok same),hy,hcy⟩
#print axioms complete
end R1Z.PV_RunJoin_RoundAssociation44
