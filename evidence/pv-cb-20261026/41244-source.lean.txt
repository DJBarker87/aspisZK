import R1Z.PV_CB_TupleProducerOffset
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerStep
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

def step (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (lane : Usize) (limbs : Array Limb 16#usize) : Result (Array Limb 16#usize) := do
  let column ← lift (Usize.wrapping_add start lane)
  let value ← offset tweak_right lane count
  let r ← lift (UScalar.cast .U16 row)
  let c ← lift (UScalar.cast .U8 column)
  Array.update limbs lane (.Cell {bank,cell := {row := r,column := c}} value)

theorem valid (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (lane : Usize) (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    PV_CB_PartialForward.Post Valid (step row start count tweak_right bank lane limbs) := by
  obtain ⟨value,hv,vv⟩ := canonical tweak_right lane count
  simp only [step,hv,lift,bind_tc_ok]
  exact PV_CB_TupleProducerOffset.update limbs vl lane _ value vv
#print axioms valid
end R1Z.PV_CB_TupleProducerStep
