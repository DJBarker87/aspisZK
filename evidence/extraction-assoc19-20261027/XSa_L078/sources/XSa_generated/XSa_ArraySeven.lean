import XSa_PowersDimensions
import XSa_PartCanonical
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XSa_ArraySeven

theorem update {A : Type} {N : Usize} (a : Array A N) (i : Usize) (v : A) (hi : i.val<N.val) :
 Array.update a i v=ok (a.set i v) := by
 obtain ⟨out,hr,he⟩ := WP.spec_imp_exists (Array.update_spec a i v (by simpa only [a.property] using hi))
 exact hr.trans (congrArg ok he)

theorem canonical_set (a : Seven) (ha : canonical a) (i : Usize) (hi : i.val<7)
 (v : C.E) (hv : XRy_WideMultiply.Canonical v) : canonical (a.set i v) := by
 intro j hj
 unfold cell
 rw [Array.set_val_eq,List.getElem_set]
 split
 · exact hv
 · exact ha j hj

#print axioms update
#print axioms canonical_set
end XSa_ArraySeven
