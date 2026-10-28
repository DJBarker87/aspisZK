import R1Z.PV_RunJoin_RoundFibreThread44
import R1Z.PV_RunJoin_RoundLaneValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundFibreValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundLoop48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (q w xs : Nat → Raw)
    (hq : ∀ k, k < 1024 → canonical (q k)) (hw : ∀ k, k < 1024 → canonical (w k))
    (hxs : ∀ k, k < 7 → canonical (xs k))
    (d : Usize) (n : Nat) (bound : d.val + n = count.val / 4) (small : count.val / 4 ≤ 256) :
    ∃ ys : Nat → Raw,
      @PV_RunJoin_RoundFibreThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) n (array 7#usize xs) d = .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = value (xs k) + terms q w (PV_RunJoin_RoundTerms44.fibres n d) k := by
  induction n generalizing xs d with
  | zero =>
    exact ⟨xs,rfl,hxs,fun k hk => by simp only [PV_RunJoin_RoundTerms44.fibres,
      ProverCommitCounterList48.counters,List.flatMap_nil,terms,add_zero]⟩
  | succ n ih =>
    obtain ⟨next,hn,hcn,hdn⟩ := PV_RunJoin_RoundLaneValue44.complete ops count q w xs hq hw hxs
      d 0#usize (by omega) (by omega) 4 (by rfl)
    obtain ⟨ys,hy,hcy,hdy⟩ := ih next hcn (Usize.wrapping_add d 1#usize)
      (by rw [PV_RunJoin_MergeLoop35.increment d (by omega)];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · simp only [PV_RunJoin_RoundFibreThread44.phase,PV_RunJoin_RoundFibreThread44.step,hn,bind_tc_ok,hy]
    · intro k hk
      rw [hdy k hk,hdn k hk,PV_RunJoin_RoundTerms44.fibres_cons,PV_RunJoin_RoundTerms44.terms_append]
      exact add_assoc _ _ _
#print axioms complete
end R1Z.PV_RunJoin_RoundFibreValue44
