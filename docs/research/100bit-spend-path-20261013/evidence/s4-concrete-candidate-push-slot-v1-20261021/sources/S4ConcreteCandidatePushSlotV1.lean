import S4ConcreteKernelOpsRootV1
import CandidatePushCheckedQBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsS4ConcreteCandidatePushSlotV1

abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev Wide := AspisR1EbyKPushDotBackend.PushWide
abbrev QM := AspisR1EbyKPushDotBackend.PushQm

/-- The concrete installed S4 `ebyKPush` slot is precisely the retained
candidate checked-Q push body. The concrete field is definitionally assigned
to `pushWithDotBackend QRaw`; the existing checked-Q bridge supplies the
full-result child equality. -/
theorem concrete_ebyKPush_eq_candidate
    (self : State) (value : Wide) (scalar : QM) :
    AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps.ebyKPush
        self value scalar =
      AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide
        AspisR1S4CandidatePushCheckedQBridgeV1.checkedQCandidate
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw)
        UScalar.add self value scalar := by
  calc
    AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps.ebyKPush
        self value scalar =
      AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar := rfl
    _ = AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide
        AspisR1S4CandidatePushCheckedQBridgeV1.checkedQCandidate
        (AspisR1S4DotPushCallEqualityV1.sourceDotPush
          AspisR1EbyKPushDecodedProductUpdate.QRaw)
        UScalar.add self value scalar :=
      (AspisR1S4CandidatePushCheckedQBridgeV1.candidate_push_eq_qraw_backend
        self value scalar).symm

#print axioms concrete_ebyKPush_eq_candidate

end AspisR1FastDotsS4ConcreteCandidatePushSlotV1
