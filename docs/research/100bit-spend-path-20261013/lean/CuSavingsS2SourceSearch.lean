import CuSavingsS2SourceTables
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceSearch
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups

theorem source_find (fuel : Nat) (masks : Array U16 64#usize)
    (groups target current : Usize) (mask : U16)
    (hc : current.val ≤ target.val) (ht : target.val ≤ groups.val) (hg : groups.val ≤ 12)
    (hf : target.val-current.val=fuel)
    (hskip : ∀ i : Usize, i.val<target.val → ∃ m,
      Array.index_usize masks i = .ok m ∧ m ≠ mask)
    (hfound : target.val<groups.val → Array.index_usize masks target = .ok mask) :
    old.grouped_inactive_pair_loop0_loop1 masks groups mask current = .ok target := by
  induction fuel generalizing current with
  | zero =>
    have he : current=target := UScalar.eq_of_val_eq (by omega)
    subst current
    have hbody : old.grouped_inactive_pair_loop0_loop1.body masks groups mask target = .ok (.done target) := by
      by_cases hl : target.val<groups.val
      · have hlt : target<groups := by simpa only [UScalar.lt_equiv] using hl
        simp [old.grouped_inactive_pair_loop0_loop1.body,hlt,hfound hl]
      · have hlt : ¬ target<groups := by simpa only [UScalar.lt_equiv] using hl
        simp [old.grouped_inactive_pair_loop0_loop1.body,hlt]
    unfold old.grouped_inactive_pair_loop0_loop1
    rw [loop,hbody]
  | succ fuel ih =>
    have hlt : current<groups := by simpa only [UScalar.lt_equiv] using (by omega : current.val<groups.val)
    obtain ⟨m,hm,hne⟩ := hskip current (by omega)
    obtain ⟨next,hn,hnv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=current) (y:=1#usize) (by scalar_tac))
    have hone : (1#usize).val=1 := by scalar_tac
    rw [hone] at hnv
    have hneval : m.val ≠ mask.val := by
      intro he;exact hne (UScalar.eq_of_val_eq he)
    have hbody : old.grouped_inactive_pair_loop0_loop1.body masks groups mask current = .ok (.cont next) := by
      simp [old.grouped_inactive_pair_loop0_loop1.body,hlt,hm,hneval,hn]
    have hrec := ih next (by omega) (by omega)
    unfold old.grouped_inactive_pair_loop0_loop1
    rw [loop,hbody]
    exact hrec

#print axioms source_find
end AspisR1.CuSavingsS2SourceSearch
