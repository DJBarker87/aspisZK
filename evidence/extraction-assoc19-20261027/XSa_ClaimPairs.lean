import XSa_GenericPairs
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XSa_ClaimPairs

def pairAt (k parts : Seven) (i : Nat) : C.E × C.E :=
 (k.val[i]?.getD XRy_Powers.zero,parts.val[i]?.getD XRy_Powers.zero)
def addTerm (sum : C.E) (pair : C.E × C.E) : Result C.E := do
 let term ← aspis_core.field.wide_exact.WideExact.mul pair.1 pair.2
 aspis_core.field.wide_exact.WideExact.add sum term

theorem pairs (k parts : Seven) : (List.range 7).map (pairAt k parts) = k.val.zip parts.val :=
 XSa_GenericPairs.indexed_zip k.val parts.val 7 k.property parts.property XRy_Powers.zero XRy_Powers.zero

theorem step (k parts : Seven) (sum : C.E) (i : Nat) (hi : i<7) :
 XRy_ClaimSumStep.step k parts sum (XRn_Join_usize i) = addTerm sum (pairAt k parts i) := by
 have hv := XRy_ClaimSelect.usize_value i (by omega)
 have h7 : (7#usize).val=7 := by scalar_tac
 have hb : (XRn_Join_usize i).val < (7#usize).val := by omega
 rw [XRy_ClaimSumStep.step,XRy_ArrayRead.read parts _ hb,bind_tc_ok,
   XRy_ArrayRead.read k _ hb,bind_tc_ok]
 unfold addTerm pairAt
 have hk : i<k.val.length := by rw [k.property,h7]; exact hi
 have hp : i<parts.val.length := by rw [parts.property,h7]; exact hi
 rw [List.getElem?_eq_getElem hk,List.getElem?_eq_getElem hp]
 simp only [Option.getD_some,hv]

#print axioms pairs
#print axioms step
end XSa_ClaimPairs
