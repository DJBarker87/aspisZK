import NNH_DistinctModelOuter
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctSeparated
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem source {N : Usize} (a : Array r1_pool_adapter.owned.OwnedAccount N)
 (distinct : RSL.distinctKeys (a.val.map account)=true) : NNH_DistinctModelInner.Separated a := by
 intro i j before inside
 have first : i.val < a.val.length := by omega
 have diff := NNH_DistinctKeys.indexed (a.val.map account) (NNH_DistinctKeys.pairs _ distinct)
  i.val j.val (by simpa using first) (by simpa using inside) before
 simp only [List.getElem_map,account] at diff
 intro equal
 have exactKeys : a.val[i.val].key=a.val[j.val].key := by
  simpa only [NGL_DistinctInduction.keyAt,List.getElem?_eq_getElem first,
   List.getElem?_eq_getElem inside,Option.map_some,Option.some.injEq] using equal
 exact diff (congrArg key exactKeys)
#print axioms source
end NNH_DistinctSeparated
