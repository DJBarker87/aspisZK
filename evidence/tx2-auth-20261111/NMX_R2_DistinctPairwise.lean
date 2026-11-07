import NMX_R2_DistinctOuter
set_option autoImplicit false
noncomputable section
namespace NMX_R2_DistinctPairwise
open Aeneas Aeneas.Std Result AdapterRw NGL_DistinctInduction NMX_DistinctPredicate
open NMX_R2_DistinctRange
/-- Native success means pairwise unequal actual keys; no descriptor comparisons
or field payloads are normalized. -/
theorem success {N : Usize} (a : Array Account N) (small : N.val≤7) :
 reference a = ok (.Ok ()) ↔ List.Pairwise (fun x y : Account => x.key ≠ y.key) a.val := by
 rw [NMX_DistinctPredicate.reference_success,NMX_R2_DistinctOuter.range a N.val 0#usize
  (by change 0+N.val≤7; simpa only [Nat.zero_add] using small)]
 constructor
 · intro run
   apply List.pairwise_iff_getElem.mpr
   intro i j hi hj before
   have no := run j (by change 0≤j; omega) (by change j<0+N.val; rw [← a.property]; simpa only [Nat.zero_add] using hj) i before
   simpa only [nthKey,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,
    Option.map_some,ne_eq,Option.some.injEq] using no
 · intro pairs i lower upper j earlier
   have hi : i<a.val.length := by rw [a.property]; change i<0+N.val at upper; omega
   have hj : j<a.val.length := by omega
   have no := List.pairwise_iff_getElem.mp pairs j i hj hi earlier
   simpa only [nthKey,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,
    Option.map_some,ne_eq,Option.some.injEq] using no
#print axioms success
end NMX_R2_DistinctPairwise
end
