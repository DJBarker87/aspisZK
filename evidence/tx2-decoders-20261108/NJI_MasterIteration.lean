import NJI_MasterCut
set_option autoImplicit false
namespace NJI_MasterIteration
open Aeneas Aeneas.Std Result NJI_MasterModel

/-- Instantiation of the existing std source loop, the emitted U64 capacity
callback, and K031/K032's one-step readonly native iterator. No loop-totality
or successful callback law remains a caller premise. -/
theorem source_association (it : core.slice.iter.Iter U64) (f : C) :
 (do let (answer,_) ← AspisS2StdAnySource.sourceAny NJI_StdAnyTransport.next predicate
      {ptr:=it.slice.val.drop it.i,end_or_len:=(),_marker:=()} f;ok answer)=
 (do let (answer,_) ← NJI_Any.any predicate it f;ok answer) :=
 NJI_StdAnyTransport.association predicate tooLarge callback it f

#print source_association
#print axioms source_association
end NJI_MasterIteration
