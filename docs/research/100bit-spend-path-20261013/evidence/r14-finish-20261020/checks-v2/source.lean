import Stage2FinishAccumulator
import Stage2FirstMatch
import Stage2FinishSourceFacts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2FinishChecks
open AspisR1Stage2
abbrev E := AspisWideTower.WideExact
abbrev K := AspisV8R15.ExactTowerBase.QM31Exact

/-- The frozen caller replaces only weights after pending.finish (candidate.rs:309–311).
The query-loop output and the finish input are deliberately different states. -/
def materialize (loopOut : verifier.Accumulator) (weights : alloc.vec.Vec Stage2K) : verifier.Accumulator :=
  { loopOut with weights := weights }

/-- Exactly the three Checks fields provided here on one literal reader/data
and query list. The boundary/final-value equations are in pairingChecks. -/
structure Fields (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) (rho : E) : Prop where
  pairingChecks : LiteralPairingChecks.checks rs
  firstMatch : ∀ j, MatchingSupport.match0 d (q j)
  residualBatch : ∑ j : Fin 22,
    (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
      QueryResidualBridge.residuals d q j = 0

/-- Conditional R14 composition: exact source shape/digest, twelve ordered
resumed queries, and finish yield the three model fields. Every unresolved
source/model frontier is a named typed law, not a Checks hypothesis. -/
theorem finish_checks_fields {W H : Type}
    (parseOps : AspisR1Stage2ContinuationParse.ParseShapeOps) (resumeOps : ResumeOps)
    (digestInst : aspis_core.digest.Digest32 H)
    (digestCompare : ∀ (s : Slice U8) (a : Array U8 32#usize),
      resumeOps.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (ops : Stage2Finish.FinishOps W) (aops : AccumulateOps) (qops : QueryOps)
    (decode : Stage2Finish.E → E) (compare : Stage2FinishPairing.ComparisonLaw ops decode)
    (checkpoint proof publicBytes : Slice U8) (hash : H) (v : verifier.View)
    (p : verifier.Prepared) (saved loopOut : verifier.Accumulator)
    (finalWeights : alloc.vec.Vec Stage2K)
    (pending pendingFinal : verifier.BatchedWeights) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) (rho : E)
    (weights : Fin 64 → K)
    (reader_R12_R13 : LiteralMatchingData.read rs = some d)
    (pairing_S3_S5_S9 : Stage2FinishPairing.PairingLaws ops decode v p d)
    (queries_R13_S4_S5_S7 : Stage2FirstMatch.QueryLaws qops decode proof p g geometry d q)
    (saved_R15_R13 : Stage2FirstMatch.Prefix d q saved)
    (dot_S5 : Stage2FinishAccumulator.DotLaw ops decode LiteralOpeningView.eK v (materialize loopOut finalWeights) d weights)
    (accumulator_S8_R15 : Stage2FinishAccumulator.Invariant decode LiteralOpeningView.eK
      (materialize loopOut finalWeights) d q (SelectedChallengeMap.rhoOf rho) weights)
    (two : ops.folds p.variant = ok 2#usize) (start : saved.next.val = 10)
    (parsed : AspisR1Stage2ContinuationParse.verifier.candidate.parse_shape parseOps proof = ok (.Ok .S2))
    (resumed : verifier.resumeWithOps resumeOps digestInst checkpoint proof publicBytes .S2 hash =
      ok (.Ok (p,saved)))
    (queried : verifier.candidate.query_loop (stage2QueryCall aops qops)
      proof p saved g obs geometry pending 22#usize = ok (.Ok (loopOut,pendingFinal)))
    (finished : Stage2Finish.verifier.finishRelationWithOps ops v p (materialize loopOut finalWeights) obs = ok (.Ok ())) :
    Stage2Finish.ShapeDigestFacts digestInst checkpoint proof hash ∧
    Fields rs d q rho := by
  refine ⟨Stage2Finish.shape_digest_facts parseOps resumeOps digestInst digestCompare
    checkpoint proof publicBytes hash p saved parsed resumed, ?_⟩
  refine ⟨Stage2FinishPairing.finish_pairingChecks ops decode compare v p (materialize loopOut finalWeights) obs rs d
    reader_R12_R13 pairing_S3_S5_S9 two finished, ?_, ?_⟩
  · exact Stage2FirstMatch.twelve_queries_firstMatch aops qops decode proof p g obs geometry
      d q queries_R13_S4_S5_S7 saved loopOut pending pendingFinal start saved_R15_R13 queried
  · exact Stage2FinishAccumulator.finish_residualBatch ops decode compare LiteralOpeningView.eK
      v p (materialize loopOut finalWeights) obs d q (SelectedChallengeMap.rhoOf rho) weights dot_S5 accumulator_S8_R15 two finished

#print axioms finish_checks_fields
end AspisR1.Stage2FinishChecks
end
