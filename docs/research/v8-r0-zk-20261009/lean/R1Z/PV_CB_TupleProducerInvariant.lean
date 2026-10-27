import R1Z.PV_CB_TupleProducerLoop
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerInvariant
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

theorem finite (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (fuel : Nat) (i : Usize) (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    PV_CB_PartialForward.Post Valid
      (PV_CB_ForwardLoop.finite (PV_CB_TupleProducerStep.step row start count tweak_right bank) fuel i limbs) :=
  PV_CB_PartialForward.finite Valid (PV_CB_TupleProducerStep.step row start count tweak_right bank)
    (fun i state valid => PV_CB_TupleProducerStep.valid row start count tweak_right bank i state valid)
    fuel i limbs vl

theorem source (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    PV_CB_PartialForward.Post Valid
      (PV_CB_TupleProducerLoop.loop (PV_CB_ForwardRange.between 0#usize count)
        row start count tweak_right bank limbs) := by
  rw [PV_CB_TupleProducerLoop.finite row start count tweak_right bank count.val 0#usize count limbs (by simp)]
  exact finite row start count tweak_right bank count.val 0#usize limbs vl
#print axioms finite
#print axioms source
end R1Z.PV_CB_TupleProducerInvariant
