import S4TotalScannedFieldResultsRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1FastDotsConcreteKernelOpsRootV1
open AspisR1FastDotsCurrent
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)

/-- The complete selected eleven-field implementation. There is no arbitrary
base backend. The redundant array branch records the literal installer shape;
both branches are the same explicit P6 constructor. Source/Std correspondence
is not asserted by choosing this concrete record. -/
def concreteOps : FourDotsOps :=
  { arrayFromFn := fun {T F} n callback initial =>
      if n.val = 8 then AspisR1FromFnP6Generated.arrayFromFnP6 n callback initial
      else AspisR1FromFnP6Generated.arrayFromFnP6 n callback initial
    wideLimbCount := .ok 8#usize
    wideAdd := AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4
    wideFromLimbs := AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent
    wideToLimbs := AspisR1EbyKPushWideToQ.toLimbs
    m31ReduceU64 := AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
    m31FromBytes := AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes
    qm31FromBytes := AspisR1FastDotsCurrentQmParserRootV1.parser
    ebyKNew := AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource
    ebyKPush := AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1EbyKPushDecodedProductUpdate.QRaw
    ebyKFinish := AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent }

theorem installed_eq_concrete (base : FourDotsOps) :
    AspisR1FastDotsFourCallbacksForwardRootV1.install base = concreteOps := by rfl

theorem concrete_array_constructor {T F : Type} (n : Usize)
    (callback : core.ops.function.FnMut F Usize T) (initial : F) :
    concreteOps.arrayFromFn n callback initial =
      AspisR1FromFnP6Generated.arrayFromFnP6 n callback initial := by
  simp only [concreteOps,ite_self]

/-- Original generated/P6 arithmetic with a fully specified operation record.
Upstream scanner/powers inputs remain explicit; there is no arbitrary Ops
parameter or independently assumed source call success. -/
theorem original_four_total_and_field_results
    (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8) (g : Array Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : g = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (values : Array Wide 4#usize) (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      fast_dots.four_dots concreteOps q g = .ok values ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ values.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps concreteOps) a g 0#usize v0 ∧
      LiteralFieldResult (literalOps concreteOps) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps concreteOps) a g 2#usize v2 ∧
      LiteralFieldResult (literalOps concreteOps) a g 3#usize v3 := by
  obtain ⟨values,a,v0,v1,v2,v3,hfixed,ha,hcan,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsTotalScannedFieldResultsRootV1.fixed_four_total_and_field_results_from_scan
      concreteOps proof j q g gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan
  have hold := AspisR1FastDotsWholeOuterTransferRootV1.installed_fixed_four_success_old_four
    concreteOps q g values hfixed
  rw [installed_eq_concrete] at hold
  exact ⟨values,a,v0,v1,v2,v3,hold,ha,hcan,hvalues,h0,h1,h2,h3⟩

#print axioms installed_eq_concrete
#print axioms concrete_array_constructor
#print axioms original_four_total_and_field_results
end AspisR1FastDotsConcreteKernelOpsRootV1
