import NMX_SmallIndices
import NMX_DistinctValues
set_option autoImplicit false
noncomputable section
namespace NMX_DistinctWindow1
open Aeneas Aeneas.Std Result AdapterRw NGL_DistinctInduction
attribute [local instance] Classical.propDecidable
theorem success (p : Account) (m : Account) (c : Account) (l : Account) (r : Account) (e : Account) (v : Account) :
 NGL_DistinctInduction.inner (Array.make 7#usize [p,m,c,l,r,e,v]) 1#usize 1 0#usize = ok none ↔
 m.key ∉ [p.key] := by
 simp [NGL_DistinctInduction.inner,keyAt,apply_ite,ite_eq_iff,
  NMX_SmallIndices.add0,NMX_SmallIndices.add1,NMX_SmallIndices.add2,
  NMX_SmallIndices.add3,NMX_SmallIndices.add4,NMX_SmallIndices.add5,NMX_SmallIndices.add6,
  and_assoc]
#print axioms success
end NMX_DistinctWindow1
end
