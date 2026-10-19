import PublicRawAmountGuard
import PublicRawCoreAgreement

/-! Fixed agreement of the shared amount predicates with the R1 raw carrier.
This Lean 4.32 module consumes only the pure core. It does not import the separate
Lean 4.31 extracted helper or establish verifier caller reachability. -/
set_option autoImplicit false
namespace AspisR1.PublicRawAmountGuardAgreement

theorem payment_guard_iff (p : PublicRawCore.Public) :
    PublicRawAmountGuard.PaymentAmountGuard p ↔
      PublicSourceRaw.PaymentAmountGuard (PublicRawCoreAgreement.fromCore p) := by
  cases p <;> rfl

theorem nonzero_iff (p : PublicRawCore.Public) :
    PublicRawAmountGuard.NonzeroWithdrawal p ↔
      PublicSourceRaw.NonzeroWithdrawal (PublicRawCoreAgreement.fromCore p) := by
  cases p <;> rfl

/-- Successful serialization plus the payment amount clause supplies the
nonzero-withdrawal option shape needed by the checked public decoder. -/
theorem decoded_of_guarded_core_success (p : PublicRawCore.Public)
    (bytes : PublicSourceRaw.Bytes)
    (hs : PublicRawCore.serialize p = some bytes)
    (hg : PublicRawAmountGuard.PaymentAmountGuard p) :
    ∃ wire, PublicSourceRaw.toWire (PublicRawCoreAgreement.fromCore p) = some wire ∧
      PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire) := by
  apply PublicSourceRawSuccess.decode_of_serialize
  · rwa [PublicRawCoreAgreement.serialize_fromCore]
  · exact (nonzero_iff p).mp (PublicRawAmountGuard.nonzero_of_payment_guard p hg)

#print axioms payment_guard_iff
#print axioms nonzero_iff
#print axioms decoded_of_guarded_core_success
end AspisR1.PublicRawAmountGuardAgreement
