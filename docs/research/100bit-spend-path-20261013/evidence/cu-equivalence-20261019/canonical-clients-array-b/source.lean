import CuSavingsCanonicalDotClientFactors
import CuSavingsLibraSourceControl
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotArray
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotClientFactors CuSavingsCanonicalDotsField
open CuSavingsLibraSourceControl

def Canonical (a : Array E 4#usize) : Prop :=
  ∀ i, i<4 → WideCanonical (lookup a field.wide_exact.WideExact.ZERO i)

theorem zero : Canonical (Array.repeat 4#usize field.wide_exact.WideExact.ZERO) := by
  intro i hi
  have hi4 : i<(4#usize).val := by scalar_tac
  simp only [lookup,Array.repeat_val,List.getD_replicate]
  simp only [show (4#usize).val=4 by scalar_tac,if_pos hi]
  simp [WideCanonical,CuSavingsCanonicalDotsField.Canonical,
    field.wide_exact.WideExact.ZERO,field.QM31.ZERO]

theorem lookup_set (a : Array E 4#usize) (i : Usize) (hi : i.val<4) (value : E) (j : Nat) :
    lookup (a.set i value) field.wide_exact.WideExact.ZERO j =
      if j=i.val then value else lookup a field.wide_exact.WideExact.ZERO j := by
  have hlen : i.val<a.val.length := by scalar_tac
  simp only [lookup,Array.set_val_eq,List.getD_eq_getElem?_getD]
  by_cases he : i.val=j
  · subst j
    rw [List.getElem?_set_self hlen]
    simp
  · rw [List.getElem?_set_ne he,if_neg (Ne.symm he)]

theorem update (a : Array E 4#usize) (i : Usize) (value : E) (hi : i.val<4) :
    Array.update a i value=.ok (a.set i value) := by
  obtain ⟨result,hr,hv⟩ := WP.spec_imp_exists (Array.update_spec a i value (by scalar_tac))
  simpa only [hv] using hr

theorem set_canonical (a : Array E 4#usize) (i : Usize) (hi : i.val<4) (value : E)
    (ha : Canonical a) (hv : WideCanonical value) : Canonical (a.set i value) := by
  intro j hj
  rw [lookup_set a i hi value j]
  split
  · exact hv
  · exact ha j hj

theorem reads_canonical (a : Array E 4#usize) (ha : Canonical a) : CanonicalArray a := by
  intro index value h
  by_cases hi : index.val<a.val.length
  · have bound : index.val<4 := by scalar_tac
    have hr := read a field.wide_exact.WideExact.ZERO index (by scalar_tac)
    have hc := ha index.val bound
    rw [h] at hr
    cases Result.ok.inj hr
    exact hc
  · unfold Array.index_usize at h
    simp only [Array.getElem?_Usize_eq,List.getElem?_eq_none (by omega)] at h
    cases h

#print axioms zero
#print axioms update
#print axioms set_canonical
#print axioms reads_canonical
end AspisR1.CuSavingsCanonicalDotArray
