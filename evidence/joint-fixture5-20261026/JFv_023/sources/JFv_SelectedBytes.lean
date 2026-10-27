import JFv_Consecutive
set_option autoImplicit false
namespace AspisR1.JFv_SelectedBytes
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft

theorem equality (input output : Slice U8) (start n : Nat) (length : output.length=n)
    (bound : start+n ≤ input.length)
    (same : ∀ j : Nat, (h : j<n) → output.val[j]'(by change output.val.length=n at length;omega) =
      input.val[start+j]'(by change start+n ≤ input.val.length at bound;omega)) :
    output.val=(input.val.drop start).take n := by
  apply List.ext_getElem
  · change output.val.length=n at length
    change start+n ≤ input.val.length at bound
    simp only [List.length_take,List.length_drop,length]
    omega
  · intro j hi hj
    rw [List.getElem_take,List.getElem_drop]
    exact same j (by change output.val.length=n at length;omega)

theorem canonical_slice (input output : Slice U8) (start n : Nat) (length : output.length=n)
    (bound : start+n ≤ input.length) (a : start%4=0) (z : n%4=0)
    (canon : OraclePortCompactDraft.canonical (bytesOf input.val))
    (same : ∀ j : Nat, (h : j<n) → output.val[j]'(by change output.val.length=n at length;omega) =
      input.val[start+j]'(by change start+n ≤ input.val.length at bound;omega)) :
    OraclePortCompactDraft.canonical (bytesOf output.val) := by
  rw [equality input output start n length bound same]
  simp only [bytesOf,List.map_take,List.map_drop]
  exact JFv_CanonicalSlice.selected (bytesOf input.val) start n a z
    (by simpa only [bytesOf,List.length_map] using bound) canon

#print axioms equality
#print axioms canonical_slice
end AspisR1.JFv_SelectedBytes
