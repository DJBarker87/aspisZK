import WithdrawalCarrierBridge431
import PublicRawAmountGuardAgreement
import R1PublicSourceBoundary
import R1PublicCodecAgreement

/-! UNCOMPILED CANDIDATE: requires the extracted modules and their Aeneas
dependencies to be checked in the same Lean 4.32 environment as the R1 codecs.
Historical Lean 4.31 receipts do not check this composition.

The input projection and byte conversion are fixed by RawBridge431. These
statements concern the actual generated Lean computations, including an explicit
payment-helper success premise. They do not assert Rust/extraction refinement,
verifier caller reachability, or account/omitted-metadata binding. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1

namespace AspisR1PublicSerializer.ExtractedPublicCheckedBridge432

/-- Every coordinate comes from the previously fixed serializer projection. -/
def projectRaw (p : Whole431.Public) : PublicSourceRaw.Public :=
  PublicRawCoreAgreement.fromCore (RawBridge431.project p)

/-- Instantiates the existing refinement contract for the extracted computation,
not for an assumed Rust-runtime semantics. No projection is chosen from bytes. -/
theorem extracted_serializer_refines :
    PublicSourceBoundary.SourceSerializerRefines RawBridge431.ExtractedReturns
      projectRaw := by
  intro p bytes hs
  change PublicSourceRaw.serialize
    (PublicRawCoreAgreement.fromCore (RawBridge431.project p)) = some bytes
  rw [PublicRawCoreAgreement.serialize_fromCore]
  exact RawBridge431.extracted_refines_core p bytes hs

/-- This is only the amount consequence of the separately extracted helper. -/
theorem helper_success_amount_guard (p : WithdrawalCarrier431.SerializerPublic)
    (t : Whole431.Transition) (hv : WithdrawalCarrier431.HelperValidated p) :
    PublicSourceRaw.PaymentAmountGuard (projectRaw (.Withdrawal p t)) := by
  exact (PublicRawAmountGuardAgreement.payment_guard_iff _).mp
    (WithdrawalCarrier431.helper_success_raw_amount_guard p t hv)

/-- Two actual generated successes on the same withdrawal public produce the
live hpub premise for the uniquely decoded fixed projection. An independently
supplied caller public still requires its own equality/binding proof. -/
theorem validated_source_parsePublic (p : WithdrawalCarrier431.SerializerPublic)
    (t : Whole431.Transition) (out : FieldsRefinement431.ByteVec)
    (hv : WithdrawalCarrier431.HelperValidated p)
    (hs : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal p t) = ok (.Ok out)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw (.Withdrawal p t)) = some wire ∧
      SemanticPublicWire.parsePublic (out.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨hraw, hguard, _⟩ := WithdrawalCarrier431.validated_source_success p t out hv hs
  obtain ⟨wire, hw, hd⟩ := PublicRawAmountGuardAgreement.decoded_of_guarded_core_success
    (RawBridge431.project (.Withdrawal p t)) (out.val.map RawBridge431.rawByte)
    hraw hguard
  exact ⟨wire, hw, PublicCodecAgreement.parsePublic_of_decode _ _ hd⟩

#print axioms extracted_serializer_refines
#print axioms helper_success_amount_guard
#print axioms validated_source_parsePublic

end AspisR1PublicSerializer.ExtractedPublicCheckedBridge432
