import R1Z.PV_RunJoin_RoundLaneThread44
import R1Z.PV_RunJoin_RoundCellValue44
import R1Z.PV_RunJoin_RoundTerms44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundLaneValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundStep48 ProverCommitRoundLoop48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (q w xs : Nat → Raw)
    (hq : ∀ k, k < 1024 → canonical (q k)) (hw : ∀ k, k < 1024 → canonical (w k))
    (hxs : ∀ k, k < 7 → canonical (xs k))
    (d s : Usize) (hd : d.val < 256) (size : 4*d.val + 4 ≤ count.val)
    (n : Nat) (bound : s.val + n = 4) :
    ∃ ys : Nat → Raw,
      @PV_RunJoin_RoundLaneThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) d n (array 7#usize xs) s = .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = value (xs k) +
        terms q w (PV_RunJoin_RoundTerms44.lanes n d s) k := by
  induction n generalizing xs s with
  | zero =>
    exact ⟨xs,rfl,hxs,fun k hk => by simp only [PV_RunJoin_RoundTerms44.lanes,ProverCommitCounterList48.counters,List.flatMap_nil,terms,add_zero]⟩
  | succ n ih =>
    obtain ⟨next,hn,hcn,hdn⟩ := PV_RunJoin_RoundCellValue44.complete ops count q w xs hq hw hxs d s 0#usize hd size (by omega) 4 (by rfl)
    obtain ⟨ys,hy,hcy,hdy⟩ := ih next hcn (Usize.wrapping_add s 1#usize)
      (by rw [PV_RunJoin_MergeLoop35.increment s (by omega)];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · simp only [PV_RunJoin_RoundLaneThread44.phase,PV_RunJoin_RoundLaneThread44.step,hn,bind_tc_ok,hy]
    · intro k hk
      rw [hdy k hk,hdn k hk,PV_RunJoin_RoundTerms44.lanes_cons,PV_RunJoin_RoundTerms44.terms_append]
      exact add_assoc _ _ _
#print axioms complete
end R1Z.PV_RunJoin_RoundLaneValue44
