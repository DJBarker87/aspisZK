import ExtractedWithdrawalCallerCarrier
import ExtractedPublicCheckedBridge432

/-! Composition of two actual extracted successes on a fixed all-field carrier.
The ASWP encoder success discharges the payment-helper premise. The separate
semantic serializer equation remains an explicit premise on that same carrier.
An independently supplied verifier public needs the stated equality to the
fixed projection; neither caller reachability nor omitted metadata binding is
asserted here. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer

namespace AspisR1WithdrawalCaller.CallerPublic

/-- The carrier is fixed before observing either output byte string. -/
def projectRaw (p : Carrier.Public) (t : Whole431.Transition) :
    PublicSourceRaw.Public :=
  ExtractedPublicCheckedBridge432.projectRaw (.Withdrawal (Carrier.toSerializer p) t)

/-- ASWP success supplies the actual payment-helper success required by the
existing extracted serializer-to-live-parser bridge. -/
theorem encoder_serializer_parsePublic
    (p : Carrier.Public) (aswp : Array U8 216#usize)
    (t : Whole431.Transition) (out : FieldsRefinement431.ByteVec)
    (he : pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p =
      ok (.Ok aswp))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (Carrier.toSerializer p) t) = ok (.Ok out)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw p t) = some wire ∧
      SemanticPublicWire.parsePublic (out.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  exact ExtractedPublicCheckedBridge432.validated_source_parsePublic
    (Carrier.toSerializer p) t out (Carrier.encoder_success_helper p aswp he) hs

/-- This equality is the remaining binding obligation for a separately supplied
public. It is not inferred from encoder success or from the ASWP bytes. -/
theorem encoder_serializer_supplied_public
    (p : Carrier.Public) (aswp : Array U8 216#usize)
    (t : Whole431.Transition) (out : FieldsRefinement431.ByteVec)
    (he : pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p =
      ok (.Ok aswp))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (Carrier.toSerializer p) t) = ok (.Ok out))
    (wire : SemanticPublicWire.Wire)
    (hw : PublicSourceRaw.toWire (projectRaw p t) = some wire)
    (supplied : R0P.Public SemanticPublicWire.M31)
    (hbind : supplied = SemanticPublicWire.toPublic wire) :
    SemanticPublicWire.parsePublic (out.val.map RawBridge431.rawByte) = some supplied := by
  obtain ⟨wire', hw', hp⟩ := encoder_serializer_parsePublic p aswp t out he hs
  have hwire : wire' = wire := Option.some.inj (hw'.symm.trans hw)
  rw [hwire, ← hbind] at hp
  exact hp

#print axioms encoder_serializer_parsePublic
#print axioms encoder_serializer_supplied_public

end AspisR1WithdrawalCaller.CallerPublic
