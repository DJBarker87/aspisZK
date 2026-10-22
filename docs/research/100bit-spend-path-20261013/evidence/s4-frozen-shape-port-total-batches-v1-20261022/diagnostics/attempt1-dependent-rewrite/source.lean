import S4ScannedClaimPowersForwardRootV1
import S4FourSlotCurrentArraySemanticsV1
import S4ScannedOpeningDecodeV1
import S4ClaimPowersSemanticV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S4FrozenShapePortTotalBatchesV1

open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

/-- Totality and exact mathematical outputs of the original extracted four-dot
control body at its explicitly installed P6/library operations. This is not the
fixed-call V10 candidate. It does not establish that the installed operations
refine the frozen Rust library or that an enclosing caller installs this port. -/
theorem frozen_shape_port_total_exact_batches
    (proof : Slice U8) (j : Nat) (q : Slice U8)
    (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : g = claimArrayToFast powers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (ha : a.val = q.val.slice 0 (608#usize)) :
    ∃ (values : Array Wide 4#usize) (c1 : C1) (c2 : C2),
      AspisR1FastDotsCurrent.fast_dots.four_dots (install concreteOps) q g = .ok values ∧
      (∀ x ∈ values.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      values.val.map (fun x => AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) =
        List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) := by
  obtain ⟨values,v0,v1,v2,v3,hsource,hcanonical,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsScannedClaimPowersForwardRootV1.four_dots_forward_of_scanner_and_claim_powers
      concreteOps proof j q a g gamma powers hgamma hpowers hcaller hlen hj hread hscan ha
  obtain ⟨c1,c2,hd1,hd2,hbytes⟩ :=
    AspisR1.S4ScannedOpeningDecodeV1.scanned_opening_decode
      proof j q a hlen hj hread hscan ha
  have hexact := AspisR1.S4ClaimPowersSemanticV1.successful_powers_exact
    gamma powers hgamma hpowers
  rw [← hcaller] at hexact
  have hmeaning :=
    AspisR1S4FourSlotCurrentArraySemanticsV1.four_slot_values_are_first_fold_fibres
      a g values v0 v1 v2 v3 hvalues
      (AspisR1CurrentPreparedClaim.Concrete.decode gamma) c1 c2 hbytes hexact h0 h1 h2 h3
  exact ⟨values,c1,c2,hsource,hcanonical,hd1,hd2,hmeaning⟩

#print axioms frozen_shape_port_total_exact_batches

end AspisR1.S4FrozenShapePortTotalBatchesV1
