import LIB_VCarriers
set_option autoImplicit false
namespace LIB_VReads
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (toRaw)
/-- The fixed last-cell read includes the native array operation and its full
Result; the bound follows from the SAME K29 carrier, without a premise. -/
theorem at28_native (a : K29) :
 Array.index_usize (k29Raw a) 28#usize=.ok (toRaw (at28 a)) := by
 obtain ⟨q,run,value⟩ := WP.spec_imp_exists
  (Array.index_usize_spec (k29Raw a) 28#usize (by
   have size : (k29Raw a).val.length=29 := (k29Raw a).property
   change 28<(k29Raw a).val.length
   omega))
 simpa only [value,k29Raw,LIB_VScalarCarriers.array,List.getElem_map,at28] using run
#print axioms at28_native
end LIB_VReads
