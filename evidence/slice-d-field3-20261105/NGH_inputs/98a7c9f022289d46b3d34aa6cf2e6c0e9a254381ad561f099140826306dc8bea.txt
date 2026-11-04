import NGH_SmallRef
import NGA_WrapperValues
set_option autoImplicit false
namespace NGH_SmallValue
open Aeneas Aeneas.Std Result NGA_PreparePairs

theorem cohort (pairs : List Input) (arity : pairs.length≤4)
 (canonical : ∀ pair∈pairs, Canonical pair.1 ∧ Canonical pair.2) :
 ∃ out, NGH_SmallRef.run pairs=ok out ∧ Canonical out ∧
 AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts pairs := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_SumAlgebra.source pairs arity canonical
 exact ⟨out,(NGH_SmallRef.model_eq pairs).trans ho,hc,hv⟩

theorem same_arrays {n : Usize} (left right : Array Q n)
 (arity : n.val≤4) (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 NGH_SmallRef.run (left.val.zip right.val)=NGA_Wrappers.small left right ∧
 ∃ out, NGH_SmallRef.run (left.val.zip right.val)=ok out ∧ Canonical out ∧
 AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=
 NGA_SumAlgebra.sumProducts (left.val.zip right.val) := by
 obtain ⟨length,domain⟩ := NGA_Wrappers.domain left right hl hr
 exact ⟨NGH_SmallRef.model_eq _,cohort _ (by rw [length];exact arity) domain⟩
#print axioms cohort
#print axioms same_arrays
end NGH_SmallValue
