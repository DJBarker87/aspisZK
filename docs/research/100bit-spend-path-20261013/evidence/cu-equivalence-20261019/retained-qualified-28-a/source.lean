import CuSavingsS2SourceTables
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceArrays
open Aeneas Aeneas.Std Result AspisR1S2Groups
abbrev E := field.wide_exact.WideExact
abbrev zero : E := field.wide_exact.WideExact.ZERO
abbrev Masks := Array U16 64#usize
abbrev OldCoeffs := Array E 64#usize
abbrev NewCoeffs := Array E 12#usize

def lookup {T : Type} {N : Usize} (a : Array T N) (default : T) (i : Nat) : T := a.val.getD i default

theorem read {T : Type} {N : Usize} (a : Array T N) (default : T) (i : Usize)
    (hi : i.val<a.val.length) : Array.index_usize a i = .ok (lookup a default i.val) := by
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hi)
  have he : out = lookup a default i.val := hv.trans (List.getD_eq_getElem a.val default hi).symm
  simpa only [he] using hr

theorem update {T : Type} {N : Usize} (a : Array T N) (i : Usize) (v : T)
    (hi : i.val<a.val.length) : Array.update a i v = .ok (a.set i v) := by
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists (Array.update_spec a i v hi)
  simpa only [hv] using hr

theorem lookup_set {T : Type} {N : Usize} (a : Array T N) (default : T)
    (i : Usize) (hi : i.val<a.val.length) (v : T) (j : Nat) :
    lookup (a.set i v) default j = if j=i.val then v else lookup a default j := by
  simp only [lookup,Array.set_val_eq,List.getD_eq_getElem?_getD]
  by_cases he : i.val=j
  · subst j
    rw [List.getElem?_set_self hi]
    simp
  · rw [List.getElem?_set_ne he,if_neg (Ne.symm he)]

def CoeffEq (old : OldCoeffs) (new : NewCoeffs) : Prop :=
  ∀ i : Nat, i<12 → lookup old zero i = lookup new zero i

theorem coeff_update (old : OldCoeffs) (new : NewCoeffs) (group : Usize)
    (hg : group.val<12) (h : CoeffEq old new) (v : E) :
    CoeffEq (old.set group v) (new.set group v) := by
  intro i hi
  rw [lookup_set old zero group (by simpa only [old.property,show (64#usize).val=64 by scalar_tac] using (by omega : group.val<64)),
    lookup_set new zero group (by simpa only [new.property,show (12#usize).val=12 by scalar_tac] using hg)]
  by_cases he : i=group.val <;> simp only [he,↓reduceIte]
  exact h i hi

def Catalog (pos : Nat) (masks : Masks) (groups : Usize) : Prop :=
  groups.val=CuSavingsS2SourceTables.seen pos ∧ ∀ i : Nat, i<groups.val →
    (lookup masks 0#u16 i).val=CuSavingsS2Tables.masks.getD i 0

#print axioms read
#print axioms update
#print axioms lookup_set
#print axioms coeff_update
end AspisR1.CuSavingsS2SourceArrays
