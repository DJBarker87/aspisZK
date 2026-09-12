import ExtractionCollectorFinalMatrix
import FSV7SelectedBodyScript

/-!
# Successful same-environment replay records

This leaf records the narrow provenance needed before a body can be used by
the permitted-access matrix.  The body may vary per replay, while `z`, root
cuts, initial digest, and source callbacks are fixed by the surrounding
`SuccessfulReplay` type.  The record itself is constructed by an actual
successful `wholeStagedScript` run.

The root theorem below deliberately exposes the remaining chronological
coupling: the selected suffix must start from a log-consistent oracle and its
actual run must succeed.  Those are run/resource obligations, not stored root
equalities and not extractor-success premises.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace AspisV8Completion.ExtractionCollectorSuccessfulReplay

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSInterleavedSelectedIncrementBoundary
open ExtractionCollectorAuthenticatedReplayable
open FSQuerySchedule FSV7PrefixBridge
open AspisV8Completion.ExtractionCollectorFinalMatrix
open AspisV8Completion.FSV7SelectedBodyScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev RootCuts := FSBoundedTranscript.RootCuts
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer

/-- One actual successful staged replay under one fixed environment. -/
structure SuccessfulReplay {n m : Nat}
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m) where
  body : Bytes
  tape : Tape
  oracle : Oracle
  record : FSAuthenticatedInterleavedPrefixMiddle.Record body z
  finalDigest : Block
  success :
    (run tape (wholeStagedScript firstWork secondWork z cuts body initialDigest)
      oracle).1 = some (.ok record, finalDigest)

/-- Projection to the matrix's permitted-access replay record. -/
def SuccessfulReplay.toReplayRecord {n m : Nat}
    {z : Fin 10 → K} {cuts : RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) :
    ReplayRecord z :=
  ⟨replay.body, replay.record⟩

theorem toReplayRecord_body {n m : Nat}
    {z : Fin 10 → K} {cuts : RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) :
    replay.toReplayRecord.body = replay.body := rfl

theorem toReplayRecord_run {n m : Nat}
    {z : Fin 10 → K} {cuts : RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork) :
    replay.toReplayRecord.run = replay.record := rfl

/-- The existing selected-body/Merkle construction derives parser roots from
the actual successful suffix run.  No root equality is stored in
`SuccessfulReplay`. -/
theorem parsed_body_roots_equal_cuts {n m : Nat}
    {z : Fin 10 → K} {cuts : RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (coherent : FSExposureOrder.LogConsistent replay.oracle) :
    ∃ wire, AspisV8.SelectedWireBytes.parse (encode replay.body) = some wire ∧
      wire.roots 0 = root208 cuts.c1 ∧
      wire.roots 1 = root208 cuts.c2 := by
  obtain ⟨staged, middleDigest, prefixSuccess, suffixSuccess⟩ :=
    successful_wholeStaged_components firstWork secondWork z cuts replay.body
      initialDigest replay.tape replay.oracle replay.record replay.finalDigest
      replay.success
  have suffixCoherent := FSExposureOrder.run_log_consistent replay.tape
    (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
    replay.oracle coherent
  obtain ⟨valid, count, _valid, _count, suffixRun⟩ :=
    successful_suffixContinuation_components cuts replay.body z middleDigest staged
      replay.tape (run replay.tape
        (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
        replay.oracle).2 replay.record replay.finalDigest suffixSuccess
  let positions := (scheduleOf staged.middle.middle.queries valid count).positions
  obtain ⟨bytes, selectedRun, increment, laterRun⟩ :=
    interleaved_ok_constructs_selected_and_increment cuts positions replay.body
      middleDigest staged.middle.functional.data staged.middle.middle.alpha0
      staged.middle.middle.rho replay.tape
      (run replay.tape
        (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
        replay.oracle).2 replay.record.suffix replay.finalDigest suffixRun
  have selectedSuccess :
      (run replay.tape (selectedScript cuts positions (encode replay.body))
        (run replay.tape
          (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
          replay.oracle).2).1 = some replay.record.suffix.selectedTrace := by
    simpa only [run_selected22] using selectedRun
  obtain ⟨merkle, _trace, root0, root1, _included⟩ :=
    selected_constructs replay.tape cuts positions (encode replay.body)
      (run replay.tape
        (prefixMiddleScript firstWork secondWork z replay.body initialDigest)
        replay.oracle).2 replay.record.suffix.selectedTrace suffixCoherent selectedSuccess
  exact ⟨merkle.wire, merkle.parsed, root0, root1⟩

#print axioms toReplayRecord_body
#print axioms toReplayRecord_run
#print axioms parsed_body_roots_equal_cuts

end
end AspisV8Completion.ExtractionCollectorSuccessfulReplay
