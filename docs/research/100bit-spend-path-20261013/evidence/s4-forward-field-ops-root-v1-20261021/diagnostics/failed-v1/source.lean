import S4FunctionForwardRootV1
import S4AllFourHeadDecodingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsForwardFieldOpsRootV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
 theorem forward_field_ops_same (base : Ops) :
    AspisR1FastDotsAllFourHeadDecodingV1.Outer
      (AspisR1FastDotsFourCallbacksForwardRootV1.arrayOps base) =
    AspisR1FastDotsFourCallbacksForwardRootV1.install base := by
  cases base
  congr 1
  funext T F n callback initial
  simp [AspisR1FastDotsAllFourHeadDecodingV1.Outer,
    AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps,
    AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8,
    AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFn,
    AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN8,
    AspisR1FastDotsFourCallbacksForwardRootV1.install,
    AspisR1FastDotsFourCallbacksForwardRootV1.arrayOps,
    AspisR1FastDotsFullCallbackForwardRootV1.install,
    AspisR1FastDotsHeadCoreForwardRootV1.headOps,
    AspisR1FastDotsHeadCoreForwardRootV1.outputOps,
    AspisR1FastDotsCurrentHeadTermForwardRootV1.install]
#print axioms forward_field_ops_same
end AspisR1FastDotsForwardFieldOpsRootV1
