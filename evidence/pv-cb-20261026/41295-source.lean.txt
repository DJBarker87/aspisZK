import R1Z.PV_CB_TupleProducerContract
import R1Z.PV_CB_TupleProducerCarrier
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerMetadataCarrier
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

def FullLimb (row : Usize) (bank : Bank) : PV_CB_TupleProducerCarrier.Limb → Prop
  | .Zero => True
  | .Cell src offset => src.bank = PV_CB_TupleProducerCarrier.bank bank ∧
      src.cell.row = UScalar.cast .U16 row ∧ PV_CB_CanonicalM31.Valid offset

theorem limb (row : Usize) (bank : Bank) (x : Limb)
    (vx : PV_CB_TupleProducerMetadata.LimbValid row bank x) :
    FullLimb row bank (PV_CB_TupleProducerCarrier.limb x) := by
  cases x with
  | Zero => trivial
  | Cell src offset =>
    rcases vx with ⟨hb,hr,vo⟩
    exact ⟨congrArg PV_CB_TupleProducerCarrier.bank hb,hr,vo⟩

theorem limbs (row : Usize) (bank : Bank) (xs : Array Limb 16#usize)
    (vx : PV_CB_TupleProducerMetadata.Valid row bank xs) :
    PV_CB_CanonicalArrays.Valid (FullLimb row bank) (PV_CB_TupleProducerCarrier.limbs xs) := by
  intro out member
  change out ∈ xs.val.map PV_CB_TupleProducerCarrier.limb at member
  obtain ⟨value,hv,rfl⟩ := List.mem_map.mp member
  exact limb row bank value (vx value hv)
#print axioms limb
#print axioms limbs
end R1Z.PV_CB_ProducerMetadataCarrier
