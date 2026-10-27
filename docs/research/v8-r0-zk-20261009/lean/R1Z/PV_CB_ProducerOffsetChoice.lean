import R1Z.PV_CB_ProducerOffsets
import R1Z.PV_CB_CanonicalUpdate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerOffsetChoice
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

def offset (ops : ExternalFuns) (adjust : Bool) (tweak : U32) : Result U32 :=
  if adjust then
    @aspis_core.field.M31.sub _ (ProverRwDictionaryScalar.selected ops) PV_CB_ProducerOffsets.zero tweak
  else @aspis_core.field.M31.ZERO _ (ProverRwDictionaryScalar.selected ops)

theorem canonical (ops : ExternalFuns) (adjust : Bool) (tweak : U32)
    (vt : PV_CB_CanonicalM31.Valid tweak) :
    ∃ value, offset ops adjust tweak = ok value ∧ PV_CB_CanonicalM31.Valid value := by
  cases adjust with
  | false => exact ⟨PV_CB_ProducerOffsets.zero,rfl,PV_CB_ProducerOffsets.zero_valid⟩
  | true => exact PV_CB_ProducerOffsets.subtract ops tweak vt

theorem cell (ops : ExternalFuns) (adjust : Bool) (tweak : U32)
    (vt : PV_CB_CanonicalM31.Valid tweak)
    (source : aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1) :
    ∃ value, offset ops adjust tweak = ok value ∧ OffsetValid (.Cell source value) := by
  obtain ⟨value,hv,vv⟩ := canonical ops adjust tweak vt
  exact ⟨value,hv,vv⟩

theorem empty_valid : PV_CB_CanonicalArrays.Valid OffsetValid
    (Array.repeat 16#usize aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1.Zero) :=
  PV_CB_CanonicalArrays.repeat_valid OffsetValid 16#usize _ PV_CB_ProducerOffsets.zero_limb

theorem update (limbs : Array Limb 16#usize)
    (valid : PV_CB_CanonicalArrays.Valid OffsetValid limbs) (i : Usize)
    (bound : i.val < 16)
    (source : aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1)
    (value : U32) (vv : PV_CB_CanonicalM31.Valid value) :
    ∃ out, Array.update limbs i (.Cell source value) = ok out ∧
      PV_CB_CanonicalArrays.Valid OffsetValid out :=
  PV_CB_CanonicalUpdate.update OffsetValid limbs i (.Cell source value) bound valid vv
#print axioms canonical
#print axioms cell
#print axioms empty_valid
#print axioms update
end R1Z.PV_CB_ProducerOffsetChoice
