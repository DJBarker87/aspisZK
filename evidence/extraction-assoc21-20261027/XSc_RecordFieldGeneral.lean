import XSc_RecordFieldArray
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_RecordFieldGeneral
open XSc_RecordFieldStep XSc_RecordFieldArray
def limb (xs : Limbs) (i : Fin 8) : U32 := xs.val[i.val]'(by have := xs.property; simpa using i.isLt)
theorem shape (xs : Limbs) :
 xs=array (limb xs 0) (limb xs 1) (limb xs 2) (limb xs 3)
  (limb xs 4) (limb xs 5) (limb xs 6) (limb xs 7) := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact xs.property
 · intro i hi hj
   have bound : i<8 := by simpa only [array,List.length_cons,List.length_nil] using hj
   have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
   rcases cases_i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
/-- Arbitrary raw limb-array nominal transport; no caller validity hypothesis. -/
theorem source (xs : Limbs) : mapped xs=_root_.aspis_core.field.wide_exact.WideExact.from_limbs xs := by
 have h := XSc_RecordFieldArray.source (limb xs 0) (limb xs 1) (limb xs 2) (limb xs 3)
  (limb xs 4) (limb xs 5) (limb xs 6) (limb xs 7)
 exact (congrArg mapped (shape xs)).trans
  (h.trans (congrArg _root_.aspis_core.field.wide_exact.WideExact.from_limbs (shape xs).symm))
#print axioms shape
#print axioms source
end XSc_RecordFieldGeneral
