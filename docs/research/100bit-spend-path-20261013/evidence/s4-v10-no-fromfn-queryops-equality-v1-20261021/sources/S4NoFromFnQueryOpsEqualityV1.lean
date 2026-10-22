import S4V10NoFromFnKernelRootV1
import Stage2ContinuationQueryLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4V10NoFromFnQueryOpsEqualityV1
open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1 (concreteCandidateQueryOps)
open AspisR1S4V10NoFromFnKernelRootV1 (noFromFnDots)

def noFromFnQueryOps (rest : QueryOps) : QueryOps :=
  { concreteCandidateQueryOps rest with dots := noFromFnDots }

theorem noFromFnQueryOps_eq_concrete (rest : QueryOps) :
    noFromFnQueryOps rest = concreteCandidateQueryOps rest := by
  cases rest with
  | mk opening dots inverse circle values ne line mulM doubleM oneM subM mark trace =>
    change QueryOps.mk
        AspisR1S4FullQueryValuesPrefixV1.sourceOpening
        noFromFnDots inverse circle values ne line mulM doubleM oneM subM mark trace =
      QueryOps.mk
        AspisR1S4FullQueryValuesPrefixV1.sourceOpening
        (fun q g => AspisR1FastDotsV10QueryOpsResultTransportV1.literalDots
          AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps q g)
        inverse circle values ne line mulM doubleM oneM subM mark trace
    have hd : noFromFnDots = (fun q g =>
        AspisR1FastDotsV10QueryOpsResultTransportV1.literalDots
          AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps q g) := by
      funext q g
      exact AspisR1S4V10NoFromFnKernelRootV1.no_from_fn_dots_eq_concrete
        (QueryOps.mk opening dots inverse circle values ne line mulM doubleM oneM subM mark trace) q g
    exact congrArg (fun f => QueryOps.mk
      AspisR1S4FullQueryValuesPrefixV1.sourceOpening f
      inverse circle values ne line mulM doubleM oneM subM mark trace) hd

theorem queryWithOps_eq_all_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
    verifier.candidate.queryWithOps aops (noFromFnQueryOps rest)
      proof p a g obs geometry pending =
    verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry pending := by
  rw [noFromFnQueryOps_eq_concrete]

def noFromFnQueryCall (aops : AccumulateOps) (rest : QueryOps) : QueryCall :=
  fun proof p a g obs geometry pending =>
    verifier.candidate.queryWithOps aops (noFromFnQueryOps rest)
      proof p a g obs geometry pending

def concreteCandidateQueryCall (aops : AccumulateOps) (rest : QueryOps) : QueryCall :=
  fun proof p a g obs geometry pending =>
    verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry pending

theorem query_loop_eq_all_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (end1 : Usize) :
    verifier.candidate.query_loop (noFromFnQueryCall aops rest)
      proof p a g obs geometry pending end1 =
    verifier.candidate.query_loop (concreteCandidateQueryCall aops rest)
      proof p a g obs geometry pending end1 := by
  have hcall : noFromFnQueryCall aops rest = concreteCandidateQueryCall aops rest := by
    funext proof p a g obs geometry pending
    exact queryWithOps_eq_all_results aops rest proof p a g obs geometry pending
  exact congrArg (fun call => verifier.candidate.query_loop call
    proof p a g obs geometry pending end1) hcall

#print axioms noFromFnQueryOps_eq_concrete
#print axioms queryWithOps_eq_all_results
#print axioms query_loop_eq_all_results
end AspisR1S4V10NoFromFnQueryOpsEqualityV1
