import R1Z.PV_CB_TupleProducerStep
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerMetadata
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

def LimbValid (row : Usize) (bank : Bank) : Limb → Prop
  | .Zero => True
  | .Cell source offset => source.bank = bank ∧ source.cell.row = UScalar.cast .U16 row ∧
      PV_CB_CanonicalM31.Valid offset
abbrev Valid (row : Usize) (bank : Bank) (limbs : Array Limb 16#usize) :=
  PV_CB_CanonicalArrays.Valid (LimbValid row bank) limbs

theorem initial (row : Usize) (bank : Bank) :
    Valid row bank (Array.repeat 16#usize (.Zero : Limb)) :=
  PV_CB_CanonicalArrays.repeat_valid _ _ _ True.intro

theorem step (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (lane : Usize) (limbs : Array Limb 16#usize) (vl : Valid row bank limbs) :
    PV_CB_PartialForward.Post (Valid row bank)
      (PV_CB_TupleProducerStep.step row start count tweak_right bank lane limbs) := by
  obtain ⟨value,hv,vv⟩ := canonical tweak_right lane count
  simp only [PV_CB_TupleProducerStep.step,hv,lift,bind_tc_ok]
  exact PV_CB_PartialArrayUpdate.update (LimbValid row bank) limbs vl lane _ ⟨rfl,rfl,vv⟩
#print axioms initial
#print axioms step
end R1Z.PV_CB_TupleProducerMetadata
