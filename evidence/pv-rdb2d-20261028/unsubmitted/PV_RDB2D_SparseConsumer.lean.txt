import R1Z.PV_RDB2D_SparsePublic
import R1Z.PV_RDB2D_SparseWeightsLength
import R1Z.PV_RDB2D_SparseFieldOrder
namespace R1Z.PV_RDB2D_SparseConsumer
open Aeneas Aeneas.Std Result PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape
set_option autoImplicit false

/-- Consume the concrete coordinate-product model, arbitrary-column ordered
fold and allocation/drop wrapper in one Result/world equality. -/
theorem complete {K S F : Type} (ops : PV_RDB2D_SparseWeights.WeightOps K)
    (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : PV_RDB2D_SparseResource.Handler K S F) (isBoolean : K → Bool)
    (point column : List K) (suffix : Nat) (state : State S F) :
    PV_RDB2D_SparseResource.source ops.toOps allocate deallocate handler isBoolean point column
      (fun p => PV_RDB2D_SparseWeights.build ops p (prefixLen isBoolean p) (trailing isBoolean p) suffix) state=
    PV_RDB2D_SparseResource.reference ops.toOps allocate deallocate handler isBoolean point column
      (fun p => PV_RDB2D_SparseWeights.build ops p (prefixLen isBoolean p) (trailing isBoolean p) suffix) state :=
  PV_RDB2D_SparseResource.arbitrary_column_world _ _ _ _ _ _ _ _ _

theorem no_reallocation {K S F : Type} (ops : PV_RDB2D_SparseWeights.WeightOps K)
    (point : List K) (width trailing suffix : Nat) (entries : List (Nat × K))
    (h : PV_RDB2D_SparseWeights.build ops point width trailing suffix=ok entries)
    (step : PV_RDB1_V183_ReserveWorld.Request → S → Option Nat × S)
    (address i : Nat) (active : i<2^width) (state : PV_RDB1_V183_ReserveWorld.World S F)
    (wordMax byteMax : Nat) :
    PV_RDB1_V183_ReserveWorld.native step wordMax byteMax PV_RDB2D_SparseLayout.shape
      (PV_RDB2D_SparsePush.buffer address (2^width) entries
        (PV_RDB2D_SparseWeightsLength.exact_capacity ops point width trailing suffix entries h) i) 1 state=
      ⟨.ok (),PV_RDB2D_SparsePush.buffer address (2^width) entries
        (PV_RDB2D_SparseWeightsLength.exact_capacity ops point width trailing suffix entries h) i,state⟩ :=
  PV_RDB2D_SparsePush.no_reallocation _ _ _ _ _ _ _ active _ _ _

#print axioms complete
#print axioms no_reallocation
end R1Z.PV_RDB2D_SparseConsumer
