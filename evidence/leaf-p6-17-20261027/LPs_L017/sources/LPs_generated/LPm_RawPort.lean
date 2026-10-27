import LPm_PublicState
import ClaimDotConcreteAdapterV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
namespace AspisR1.LPm_RawPort
open Aeneas Aeneas.Std Result LPi_FieldValues
abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev Native := FIo_Native.fast_pairing.EbyKDot

def statePort (s : Native) : State := ⟨⟨s.c0.sums⟩,⟨s.c1.sums⟩,s.count⟩

def qPort (x : NQ) : AspisR1CurrentPreparedClaim.aspis_core.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

def ePort (x : NE) : AspisR1CurrentPreparedClaim.Concrete.E := ⟨qPort x.c0,qPort x.c1⟩

/-- The retained cohort uses THIS same raw operation; an unrelated raw
product with the same name is never substituted. -/
theorem raw_eq (a b : FIo_Native.fast_pairing.canonical.Q) :
    AspisR1EbyKPushDecodedProductUpdate.QRaw a b =
      FIo_Native.fast_pairing.canonical.Q.raw a b := by
  change AspisR1CanonicalQRawUnified.canonical.Q.raw a b = _
  exact (LPi_RawAssociation.source_eq a b).symm

theorem state_fields (s : Native) :
    (statePort s).c0.sums=s.c0.sums ∧ (statePort s).c1.sums=s.c1.sums ∧
      (statePort s).count=s.count := ⟨rfl,rfl,rfl⟩

#print axioms raw_eq
#print axioms state_fields
#check AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
#check AspisR1FinishDotSourceABI.finishFromPush_total
#print AspisR1DotPushLocal.Proof.updatedSums
#print AspisR1EbyKPushDecodedProductUpdate.castSums
#print AspisR1EbyKPushDecodedProductUpdate.tupleAdd
end AspisR1.LPm_RawPort
