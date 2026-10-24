import Port9OR_P6Progress

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_P6Rows
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration

def rows : Nat → reference.Scratch → Slice U8 → Usize → Usize → Code reference.Level
  | 0,s,_,i,w => if i≥s.n then .done (.Done {s with n:=w}) else liftResult .div
  | fuel+1,s,physical,i,w =>
    if i≥s.n then .done (.Done {s with n:=w}) else do
      let out ← Port9OR_P6Node.node s physical i w
      match out with
      | .Stop stopped => pure (.Stop stopped)
      | .Next next ni nw => rows fuel next physical ni nw

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (physical : Slice U8) (fuel : Nat) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (bound : s.n.val-i.val≤fuel) :
    erase D hash (rows fuel s physical i w)=
      reference.level_rows (Port9OR_P6Node.digest D) hash s physical i w := by
  induction fuel generalizing s i w with
  | zero =>
    have halt : i≥s.n := by change i.val≥s.n.val; omega
    rw [reference.level_rows]
    simp only [rows,if_pos halt,erase]
  | succ fuel ih =>
    rw [reference.level_rows]
    simp only [rows,erase_ite,erase_bind,erase_pure,Port9OR_P6Node.node_source]
    by_cases halt : i≥s.n
    · simp only [if_pos halt,erase]
    · simp only [if_neg halt]
      cases ran : reference.binary_step (Port9OR_P6Node.digest D) hash s physical i w with
      | fail e => rfl
      | div => rfl
      | ok out =>
        have active : i.val<s.n.val := by change ¬i.val≥s.n.val at halt;omega
        have progress := Port9OR_P6Progress.node_progress D hash physical s i w domain active out ran
        simp only [bind_tc_ok]
        cases out with
        | Stop stopped => rfl
        | Next next ni nw =>
          obtain ⟨sameN,nextDomain,advance,_⟩ := progress
          exact ih next ni nw nextDomain (by rw [sameN];omega)

/-- Successful level preservation with the original partial primitive. -/
theorem preserve {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (physical : Slice U8) (fuel : Nat) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (written : i.val=0 ∨ 0<w.val)
    (next : reference.Scratch) (ran : erase D hash (rows fuel s physical i w)=ok (.Done next)) :
    Domain physical next := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [rows] at ran
    split at ran
    · cases ran
      obtain ⟨nonempty,bounded,_,writeBound,atBound⟩ := domain
      exact ⟨by rcases written with zero | positive <;> scalar_tac,by scalar_tac,atBound⟩
    · cases ran
  | succ fuel ih =>
    simp only [rows] at ran
    split at ran
    · cases ran
      obtain ⟨nonempty,bounded,_,writeBound,atBound⟩ := domain
      exact ⟨by rcases written with zero | positive <;> scalar_tac,by scalar_tac,atBound⟩
    · rename_i halt
      simp only [erase_bind,Port9OR_P6Node.node_source] at ran
      cases called : reference.binary_step (Port9OR_P6Node.digest D) hash s physical i w with
      | fail e => simp only [called,bind_tc_fail] at ran; cases ran
      | div => simp only [called,bind_tc_div] at ran; cases ran
      | ok out =>
        have active : i.val<s.n.val := by scalar_tac
        have progress := Port9OR_P6Progress.node_progress D hash physical s i w domain active out called
        simp only [called,bind_tc_ok] at ran
        cases out with
        | Stop stopped => cases ran
        | Next after ni nw =>
          exact ih after ni nw progress.2.1 (Or.inr (by have := progress.2.2.2;omega)) ran

#print axioms source
#print axioms preserve
end AspisR1.Port9OR_P6Rows
end
