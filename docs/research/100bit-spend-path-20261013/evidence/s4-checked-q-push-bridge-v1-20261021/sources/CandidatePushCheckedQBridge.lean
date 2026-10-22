import CandidateAllEquivalence
import AspisR1EbyKPushConcreteCheckedQV1
import EbyKCheckedQCanonicality
import S4DotPushCallEqualityV1

open Aeneas Aeneas.Std Result
namespace AspisR1S4CandidatePushCheckedQBridgeV1

abbrev CandidateQ := AspisR1CheckedQCandidateV1.Q
abbrev Qm := AspisR1EbyKPushExplicitOpsV1.Qm
abbrev Q := AspisR1EbyKPushExplicitOpsV1.Q
abbrev Wide := AspisR1EbyKPushExplicitOpsV1.Wide
abbrev Dot := AspisR1EbyKPushExplicitOpsV1.Dot
abbrev State := AspisR1EbyKPushExplicitOpsV1.State

/-- Candidate copy of the retained emitted `fast_pairing.checked_q` body.
    The sole call substitution is to the exact candidate `Q.from_limbs` body. -/
def checkedQCandidate (k : Qm) :
    Result (core.result.Result Q Unit) := do
  let a ← AspisR1EbyKCheckedQAllParamV1.limbsOf k
  let o ← AspisR1CheckedQCandidateV1.Q.from_limbs a
  AspisR1EbyKCheckedQAllParamV1.optionOkOr o ()

theorem checkedQCandidate_eq_concreteAll (k : Qm) :
    checkedQCandidate k =
      AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
        AspisR1EbyKCheckedQConcreteAll.concreteAll k := by
  unfold checkedQCandidate AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
  apply congrArg (fun f => Bind.bind (AspisR1EbyKCheckedQAllParamV1.limbsOf k) f)
  funext a
  exact congrArg
    (fun r => Bind.bind r (fun o => AspisR1EbyKCheckedQAllParamV1.optionOkOr o ()))
    (AspisR1S4CheckedQCandidateAllEquivalenceV1.generated_from_limbs_eq_existing_all_model a)

/-- Full-result equality at the explicit EbyK push slot. The bound branch,
    reject branch, both dot calls, and all Result propagation remain those of
    the retained `pushWithOps` body. -/
theorem pushWithCandidateCheckedQ_eq_concreteAll
    (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) :
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
      AspisR1EbyKPushWideToQ.fromWide checkedQCandidate pushDot UScalar.add
      self value scalar =
    AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
      AspisR1EbyKCheckedQConcreteAll.concreteAll pushDot self value scalar := by
  have hchecked : checkedQCandidate =
      AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
        AspisR1EbyKCheckedQConcreteAll.concreteAll :=
    funext checkedQCandidate_eq_concreteAll
  change AspisR1EbyKPushExplicitOpsV1.pushWithOps
      AspisR1EbyKPushWideToQ.fromWide checkedQCandidate pushDot UScalar.add
      self value scalar =
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
      AspisR1EbyKPushWideToQ.fromWide
      (AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
        AspisR1EbyKCheckedQConcreteAll.concreteAll)
      pushDot UScalar.add self value scalar
  exact congrArg
    (fun check => AspisR1EbyKPushExplicitOpsV1.pushWithOps
      AspisR1EbyKPushWideToQ.fromWide check pushDot UScalar.add self value scalar)
    hchecked

/-- The candidate checked-Q body at this push call is the installed raw Dot
    backend's full operation, with the emitted Dot loop instantiated and the
    retained candidate all-equivalence used at the checked-Q child. -/
theorem candidate_push_eq_qraw_backend
    (self : AspisR1EbyKPushDotBackend.PushState)
    (value : AspisR1EbyKPushDotBackend.PushWide)
    (scalar : AspisR1EbyKPushDotBackend.PushQm) :
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
      AspisR1EbyKPushWideToQ.fromWide checkedQCandidate
      (AspisR1S4DotPushCallEqualityV1.sourceDotPush
        AspisR1EbyKPushDecodedProductUpdate.QRaw)
      UScalar.add self value scalar =
    AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar := by
  calc
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide checkedQCandidate
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw)
        UScalar.add self value scalar =
      AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
        AspisR1EbyKCheckedQConcreteAll.concreteAll
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw) self value scalar :=
      pushWithCandidateCheckedQ_eq_concreteAll
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw) self value scalar
    _ = AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar := by
      change AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide
        (AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
          AspisR1EbyKCheckedQConcreteAll.concreteAll)
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw)
        UScalar.add self value scalar = _
      exact (AspisR1S4DotPushCallEqualityV1.qraw_backend_eq_generated_dot_control
        self value scalar).symm

#print axioms checkedQCandidate_eq_concreteAll
#print axioms pushWithCandidateCheckedQ_eq_concreteAll
#print axioms candidate_push_eq_qraw_backend
end AspisR1S4CandidatePushCheckedQBridgeV1
