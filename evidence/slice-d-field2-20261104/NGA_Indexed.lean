import NGA_OuterStep
import NGA_WrapperValues
set_option autoImplicit false
namespace NGA_Indexed
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Qm := NGA_Cache.Q

def selected {n : Usize} (xs : Array Qm n) (i : Fin n.val) : Qm :=
 xs.val[i.val]'(by simpa [xs.property] using i.isLt)

def pairs {n : Usize} (left right : Array Qm n) : List (Qm × Qm) :=
 List.ofFn (fun i : Fin n.val => (selected left i,selected right i))

theorem same_inputs {n : Usize} (left right : Array Qm n) : pairs left right=left.val.zip right.val := by
 apply List.ext_getElem
 · simp [pairs,List.length_zip,left.property,right.property]
 · intro i hi hj
   simp [pairs,selected,List.getElem_zip]

/-- Native data-independent index chronology selects exactly the same ordered
pairs as the root wrapper's two input arrays. -/
theorem full_value {n : Usize} (left right : Array Qm n) (arity : n.val≤4)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 ∃ out, NGA_Wrappers.small left right=ok out ∧ NGA_Cache.Canonical out ∧
 AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (pairs left right) := by
 rw [same_inputs]
 exact NGA_WrapperValues.source left right arity hl hr

#print axioms same_inputs
#print axioms full_value
end NGA_Indexed
