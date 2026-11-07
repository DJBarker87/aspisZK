import NMX_SmallIndices
import NMX_DistinctValues
import NMX_KeyCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_DistinctSuccess
open Aeneas Aeneas.Std Result AdapterRw
open NGL_DistinctInduction
attribute [local instance] Classical.propDecidable
/-- Seven account descriptors, not their buffers:21 symbolic key comparisons.
The generic CLOSED induction remains folded until this bounded specialization. -/
theorem seven (p m c l r e v : Account) :
 reference (Array.make 7#usize [p,m,c,l,r,e,v]) = ok (.Ok ()) ↔
 [p.key,m.key,c.key,l.key,r.key,e.key,v.key].Nodup := by
 simp [reference,outer,NGL_DistinctInduction.inner,keyAt,List.nodup_cons,
   NMX_SmallIndices.add0,NMX_SmallIndices.add1,NMX_SmallIndices.add2,NMX_SmallIndices.add3,NMX_SmallIndices.add4,NMX_SmallIndices.add5,NMX_SmallIndices.add6,apply_ite,
   eq_comm,ite_eq_iff,and_comm,and_left_comm,and_assoc]
#print axioms seven
end NMX_DistinctSuccess
end
