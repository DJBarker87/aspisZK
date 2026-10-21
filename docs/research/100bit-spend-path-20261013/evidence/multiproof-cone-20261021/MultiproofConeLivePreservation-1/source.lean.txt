import MultiproofConeLiveReference

set_option autoImplicit false
namespace AspisR1.MultiproofConeLivePreservation
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLiveOrder MultiproofConeLiveReference

def keys (s : reference.Scratch) (j : Nat) : Nat := s.idx.val[j]!.val

theorem set_keys (s : reference.Scratch) (w : Usize) (parent : U32) (bound : w.val<16)
    (i : Nat) (value : parent.val=keys s i/2) :
    keys {s with idx:=s.idx.set w parent} = write (keys s) i w.val := by
  funext j
  have len : s.idx.val.length=16 := s.idx.property
  by_cases eq : j=w.val
  · subst j
    simp [keys,write,Array.set_val_eq,List.getElem!_eq_getElem?_getD,
      List.getElem?_set_self (by omega : w.val<s.idx.val.length),value]
  · have ne : w.val≠j := Ne.symm eq
    simp [keys,write,Array.set_val_eq,List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne ne,eq]

theorem guard_eq (s : reference.Scratch) (i : Usize)
    (sorted : Strict (keys s) i.val s.n.val) :
    SourcePair s i ↔ pairAt (keys s) s.n.val i.val := by
  unfold SourcePair pairAt
  constructor
  · rintro ⟨bound,guard⟩
    refine ⟨bound,?_⟩
    have asc := sorted i.val (i.val+1) (by omega) (by omega) bound
    apply (MultiproofConeModelBoundary.paired_iff _ _ asc).mp
    unfold keys
    scalar_tac
  · rintro ⟨bound,guard⟩
    refine ⟨bound,?_⟩
    have asc := sorted i.val (i.val+1) (by omega) (by omega) bound
    have x := (MultiproofConeModelBoundary.paired_iff _ _ asc).mpr guard
    unfold keys at x
    scalar_tac

/-- Concrete extracted-array invariant preservation. This uses the checked
body's exact mutation theorem; the invariant is not an added source premise. -/
theorem binary_preserves {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (s : reference.Scratch)
    (i w : Usize) (domain : RowDomain physical s i w) (active : i.val<s.n.val)
    (inv : Inv (keys s) s.n.val i.val w.val) (next : reference.Scratch) (ni nw : Usize)
    (success : reference.binary_step D hash s physical i w=ok (.Next next ni nw)) :
    Inv (keys next) next.n.val ni.val nw.val := by
  obtain ⟨out,eqout,shape⟩ := binary_shape D hash total physical s i w domain active
  rw [success] at eqout
  cases eqout
  obtain ⟨parent,set,parentVal,advanceVal,writeVal⟩ := shape
  obtain ⟨out,eqout,progress⟩ := binary_step_progress D hash total physical s i w domain active
  rw [success] at eqout
  cases eqout
  have sameN := progress.1
  have wb : w.val<16 := by obtain ⟨_,b,_,wi,_⟩ := domain;omega
  have keyEq : keys next=write (keys s) i.val w.val := by
    have base : keys next=keys {s with idx:=s.idx.set w parent} := by
      unfold keys;rw [set]
    exact base.trans (set_keys s w parent wb i.val parentVal)
  have adv : ni.val=advance (keys s) s.n.val i.val := by
    rw [advanceVal]
    simp only [advance,guard_eq s i inv.2.2.2.1]
  rw [keyEq,sameN,adv,writeVal]
  exact step (keys s) s.n.val i.val w.val inv active

/-- Actual bounded reference rows preserve the order of their final live
prefix. Missing siblings, panic and divergence cannot witness success. -/
theorem rows_sorted {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
    (inv : Inv (keys s) s.n.val i.val w.val) (next : reference.Scratch)
    (success : rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w=ok (.Done next)) :
    Strict (keys next) 0 next.n.val := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [rows] at success
    split at success
    next => cases success;exact inv.2.2.1
    next => cases success
  | succ fuel ih =>
    simp only [rows] at success
    split at success
    next => cases success;exact inv.2.2.1
    next halt =>
      obtain ⟨out,eqout,post⟩ := binary_step_progress D hash total physical s i w domain (by scalar_tac)
      rw [eqout] at success
      simp only [bind_tc_ok] at success
      cases out with
      | Stop stopped => cases success
      | Next after ni nw =>
        exact ih after ni nw post.2.1
          (binary_preserves D hash total physical s i w domain (by scalar_tac) inv after ni nw eqout) success

theorem level_sorted {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (s next : reference.Scratch)
    (domain : MultiproofConeLevelIteration.Domain physical s) (sorted : Strict (keys s) 0 s.n.val)
    (success : reference.level_rows D hash s physical 0#usize 0#usize=ok (.Done next)) :
    Strict (keys next) 0 next.n.val := by
  have dom : RowDomain physical s 0#usize 0#usize :=
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  rw [rows_eq_extracted D hash total physical s.n.val s _ _ dom (by simp)] at success
  exact rows_sorted D hash total physical s.n.val s _ _ dom (initial (keys s) s.n.val sorted) next success

#print axioms set_keys
#print axioms guard_eq
#print axioms binary_preserves
#print axioms rows_sorted
#print axioms level_sorted
end AspisR1.MultiproofConeLivePreservation
