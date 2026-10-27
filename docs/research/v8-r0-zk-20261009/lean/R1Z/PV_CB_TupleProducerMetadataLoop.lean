import R1Z.PV_CB_TupleProducerMetadata
import R1Z.PV_CB_TupleProducerLoop
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerMetadataLoop
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

theorem finite (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (fuel : Nat) (i : Usize) (limbs : Array Limb 16#usize)
    (vl : PV_CB_TupleProducerMetadata.Valid row bank limbs) :
    PV_CB_PartialForward.Post (PV_CB_TupleProducerMetadata.Valid row bank)
      (PV_CB_ForwardLoop.finite (PV_CB_TupleProducerStep.step row start count tweak_right bank)
        fuel i limbs) :=
  PV_CB_PartialForward.finite _ _ (PV_CB_TupleProducerMetadata.step row start count tweak_right bank)
    fuel i limbs vl

theorem source (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (limbs : Array Limb 16#usize) (vl : PV_CB_TupleProducerMetadata.Valid row bank limbs) :
    PV_CB_PartialForward.Post (PV_CB_TupleProducerMetadata.Valid row bank)
      (PV_CB_TupleProducerLoop.loop (PV_CB_ForwardRange.between 0#usize count)
        row start count tweak_right bank limbs) := by
  rw [PV_CB_TupleProducerLoop.finite row start count tweak_right bank count.val 0#usize count limbs (by simp)]
  exact finite row start count tweak_right bank count.val 0#usize limbs vl
#print axioms finite
#print axioms source
end R1Z.PV_CB_TupleProducerMetadataLoop
