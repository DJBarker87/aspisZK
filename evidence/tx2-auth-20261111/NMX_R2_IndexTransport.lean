import NMX_R2_ResultRelation
import NMX_R2_HeterogeneousPrimitives
set_option autoImplicit false
namespace NMX_R2_IndexTransport
open Aeneas Aeneas.Std
/-- A source guard supplies this own-index bound. The theorem reads one
original descriptor and transports that SAME value through the carrier map. -/
theorem inside {A B : Type} (encode : A → B) (a : Slice A) (index : Usize)
 (bound : index.val < a.val.length) :
 NMX_R2_Heterogeneous.Refines encode
  (NMX_R2_ResultRelation.raw (Slice.index_usize a index))
  (RSL.RS.index (a.val.map encode) index.val) := by
 have native : Slice.index_usize a index = .ok (a.val[index.val]'bound) := by
  simp [Slice.index_usize,bound]
 rw [native]
 simp only [RSL.RS.index,List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some]
 exact NMX_R2_HeterogeneousPrimitives.pure encode (a.val[index.val]'bound)
#print axioms inside
end NMX_R2_IndexTransport
