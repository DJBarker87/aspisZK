import MultiproofConeNodeDomain

set_option autoImplicit false
namespace AspisR1.MultiproofConeNodeIteration
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeLevelIteration

abbrev Step := reference.Scratch → Usize → Usize → Result reference.Row

/-- Fuel counts remaining input nodes, not hashes. Both occupied children are
consumed in one step. The complete scratch and all non-success Results survive. -/
def rows (step : Step) : Nat → reference.Scratch → Usize → Usize → Result reference.Level
  | 0,s,i,w => if i≥s.n then ok (.Done {s with n:=w}) else div
  | fuel+1,s,i,w => if i≥s.n then ok (.Done {s with n:=w}) else do
      let out ← step s i w
      match out with
      | .Stop stopped => ok (.Stop stopped)
      | .Next next ni nw => rows step fuel next ni nw

/-- The extracted recursion agrees with the bounded node iteration. This
uses proved progress of its actual node body, not an assumed level equation. -/
theorem rows_eq_extracted {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
    (bound : s.n.val-i.val ≤ fuel) :
    reference.level_rows D hash s physical i w =
      rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w := by
  induction fuel generalizing s i w with
  | zero =>
    have halt : i≥s.n := by obtain ⟨_,_,_,_,_⟩ := domain; scalar_tac
    rw [reference.level_rows]
    simp only [halt,if_true,rows]
  | succ fuel ih =>
    rw [reference.level_rows]
    simp only [rows]
    by_cases halt : i≥s.n
    · simp only [halt,if_true]
    · simp only [halt,if_false]
      have active : i.val < s.n.val := by scalar_tac
      obtain ⟨out,eqout,post⟩ := binary_step_progress D hash total physical s i w domain active
      rw [eqout]
      simp only [bind_tc_ok]
      cases out with
      | Stop stopped => rfl
      | Next next ni nw =>
        obtain ⟨sameN,nextDomain,advance,_⟩ := post
        exact ih next ni nw nextDomain (by rw [sameN];omega)

/-- Extensional row certificates compose using the checked target's progress.
The source premise is local to ONE node pair, never to a level or height. -/
theorem rows_congr {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (source : Step)
    (certificate : ∀ s i w, RowDomain physical s i w → i.val < s.n.val →
      source s i w=reference.binary_step D hash s physical i w)
    (fuel : Nat) (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w) :
    rows source fuel s i w =
      rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w := by
  induction fuel generalizing s i w with
  | zero => rfl
  | succ fuel ih =>
    simp only [rows]
    by_cases halt : i≥s.n
    · simp only [halt,if_true]
    · simp only [halt,if_false]
      have active : i.val < s.n.val := by scalar_tac
      rw [certificate s i w domain active]
      obtain ⟨out,eqout,post⟩ := binary_step_progress D hash total physical s i w domain active
      rw [eqout]
      simp only [bind_tc_ok]
      cases out with
      | Stop stopped => rfl
      | Next next ni nw => exact ih next ni nw post.2.1

/-- A successful level has a nonempty bounded frontier; no next state is
invented for rejection, panic or divergence. -/
theorem rows_preserve {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
    (written : i.val=0 ∨ 0<w.val) (next : reference.Scratch)
    (success : rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w=ok (.Done next)) :
    Domain physical next := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [rows] at success
    split at success
    next halt =>
      cases success
      obtain ⟨nonempty,bounded,_,writeBound,atBound⟩ := domain
      exact ⟨by rcases written with zero | positive <;> scalar_tac,by scalar_tac,atBound⟩
    next => cases success
  | succ fuel ih =>
    simp only [rows] at success
    split at success
    next halt =>
      cases success
      obtain ⟨nonempty,bounded,_,writeBound,atBound⟩ := domain
      exact ⟨by rcases written with zero | positive <;> scalar_tac,by scalar_tac,atBound⟩
    next active =>
      obtain ⟨out,eqout,post⟩ := binary_step_progress D hash total physical s i w domain (by scalar_tac)
      rw [eqout] at success
      simp only [bind_tc_ok] at success
      cases out with
      | Stop stopped => cases success
      | Next after ni nw =>
        exact ih after ni nw post.2.1 (Or.inr (by have := post.2.2.2;omega)) success

/-- Concrete reference-level preservation, discharging the previous height
composition's domain premise on the extracted reference side. -/
theorem level_preserve {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (s next : reference.Scratch)
    (domain : Domain physical s)
    (success : reference.level_rows D hash s physical 0#usize 0#usize=ok (.Done next)) :
    Domain physical next := by
  have rowDomain : RowDomain physical s 0#usize 0#usize := ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  rw [rows_eq_extracted D hash total physical s.n.val s 0#usize 0#usize rowDomain (by simp)] at success
  exact rows_preserve D hash total physical s.n.val s 0#usize 0#usize rowDomain (Or.inl rfl) next success

#print axioms rows_eq_extracted
#print axioms rows_congr
#print axioms rows_preserve
#print axioms level_preserve
end AspisR1.MultiproofConeNodeIteration
