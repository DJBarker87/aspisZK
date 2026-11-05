import NGL_DistinctInduction
import NHD_DistinctAssociation
set_option autoImplicit false
noncomputable section
namespace NHJ_DistinctPacket
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev A := NGL_DistinctStep.Account
/-- The native iteration reads only the selected two keys. This transport
    identifies them across a live prefix embedding; it supplies no returned value. -/
theorem same_comparison {N M : Usize} (a : Array A N) (b : Array A M)
    (index previous : Usize)
    (ai : index.val < a.val.length) (ap : previous.val < a.val.length)
    (bi : index.val < b.val.length) (bp : previous.val < b.val.length)
    (left : (a.val[previous.val]'ap).key = (b.val[previous.val]'bp).key)
    (right : (a.val[index.val]'ai).key = (b.val[index.val]'bi).key) :
    NHD_DistinctAssociation.cut
      (decide ((a.val[previous.val]'ap).key = (a.val[index.val]'ai).key)) previous =
    NHD_DistinctAssociation.cut
      (decide ((b.val[previous.val]'bp).key = (b.val[index.val]'bi).key)) previous := by
  rw [left,right]

/-- NGL's already-proved full induction, specialized to the actual TX2 count.
    Native value/frame/negative evidence is NHD_K037/K038, not rerun here. -/
theorem seven (ops : AdapterRw.Ops) (a : Array A 7#usize) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
      (NGL_ReadonlyModel.install ops) a = NGL_DistinctInduction.reference a :=
  NGL_DistinctInduction.source ops a (by decide)

/-- The same emitted generic induction at TX1's three-account count. The actual
    inner source body has no N-dependent expression except checked array access;
    same_comparison transports the two key reads into the seven-slot native gate. -/
theorem three (ops : AdapterRw.Ops) (a : Array A 3#usize) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
      (NGL_ReadonlyModel.install ops) a = NGL_DistinctInduction.reference a :=
  NGL_DistinctInduction.source ops a (by decide)
#print axioms same_comparison
#print axioms seven
#print axioms three
end NHJ_DistinctPacket
