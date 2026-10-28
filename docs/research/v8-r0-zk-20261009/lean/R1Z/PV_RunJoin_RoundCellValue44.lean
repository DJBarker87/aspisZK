import R1Z.PV_RunJoin_RoundBodyValue44
import R1Z.PV_RunJoin_RoundTerms44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCellValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundStep48 ProverCommitRoundLoop48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (q w xs : Nat → Raw)
    (hq : ∀ k, k < 1024 → canonical (q k)) (hw : ∀ k, k < 1024 → canonical (w k))
    (hxs : ∀ k, k < 7 → canonical (xs k))
    (d s t : Usize) (hd : d.val < 256) (size : 4*d.val + 4 ≤ count.val)
    (hs : s.val < 4) (n : Nat) (bound : t.val + n = 4) :
    ∃ ys : Nat → Raw,
      @PV_RunJoin_RoundCellThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) d s n (array 7#usize xs) t = .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = value (xs k) +
        terms q w (PV_RunJoin_RoundTerms44.children n d s t) k := by
  induction n generalizing xs t with
  | zero =>
    exact ⟨xs,rfl,hxs,fun k hk => by simp only [PV_RunJoin_RoundTerms44.children,ProverCommitCounterList48.counters,List.map_nil,terms,add_zero]⟩
  | succ n ih =>
    obtain ⟨next,hn,hcn,hdn⟩ := PV_RunJoin_RoundBodyValue44.step ops count q w xs hq hw hxs d s t hd size hs (by omega)
    obtain ⟨ys,hy,hcy,hdy⟩ := ih next hcn (Usize.wrapping_add t 1#usize)
      (by rw [PV_RunJoin_MergeLoop35.increment t (by omega)];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · simp only [PV_RunJoin_RoundCellThread44.phase,hn,bind_tc_ok,hy]
    · intro k hk
      rw [hdy k hk,hdn k hk,PV_RunJoin_RoundTerms44.children_cons,terms]
      exact add_assoc _ _ _
#print axioms complete
end R1Z.PV_RunJoin_RoundCellValue44
