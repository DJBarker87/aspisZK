import ExtractionCollectorAuthenticatedReplayable
import SameBodyAuthenticatedIncrement

/-!
# Interleaved selected-opening / increment boundary

Rust reaches selected q22 Merkle calls after rho and before increment
absorption.  The current `selectedScript` returns only its
`OrderedRawQueryLog`; its final digest is returned by `run`, not by the Script
value passed to `FSTranscriptScript.bind`.  This leaf records the exact
run-level boundary and the smallest state-to-increment interface needed for an
interleaved continuation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000

namespace AspisV8Completion.FSInterleavedSelectedIncrementBoundary

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV7PrefixBridge FSV7SelectedBodyScript
open AspisV8Completion.ExtractionCollectorAuthenticatedReplayable
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.SameBodyAuthenticatedSlots
open AspisV8.SameBodyAuthenticatedFold
open AspisV8Completion.SameBodyQueryClaim AspisV8Completion.SameBodyQueryClaimExact
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCQM31Representation
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisV8.SelectedWireBytes AspisV8.SelectedPackedQueryBridge
open AspisV8.OODInterpolant
open AspisV8.PackedQueryRecord AspisV8.SelectedPackedQueryBridge
open AspisV8.LineNormBuffer
open AspisV8.SelectedQueryBuffer

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position
abbrev RootCuts := FSBoundedTranscript.RootCuts

inductive InterleavedError where
  | openedPipeline
  | alpha1 (error : FSNonzeroQM31.Error)
  | alpha2 (error : FSNonzeroQM31.Error)
  | alpha3 (error : FSNonzeroQM31.Error)
  deriving DecidableEq

structure InterleavedSuccess where
  selectedTrace : OrderedRawQueryLog
  alpha1 : QM31Exact
  alpha2 : QM31Exact
  alpha3 : QM31Exact

structure LaterSuccess where
  alpha1 : QM31Exact
  alpha2 : QM31Exact
  alpha3 : QM31Exact

/-! The arithmetic part can be factored without a hash view.  It parses the
wire, decodes the records, computes the checked inverses, and folds the opened
values.  Authentication is deliberately absent from this factor; it is the
preceding `selected22` script's separate responsibility. -/

structure PureOpenedPreparation where
  wire : AspisV8.SelectedWireBytes.Wire
  decoded : Fin 22 -> AspisV8.PackedQueryRecord.Decoded
  inverses : List QM31Exact × List AspisV5ComponentCQM31TowerExact.M31Exact

def pureOpenedPreparation (body : Bytes) (query : Fin 22 -> Position)
    (data : Data (K := QM31Exact)) : Option PureOpenedPreparation := do
  let wire ← AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin)
  let decoded ← parseRecords wire
  let inverses ← inverseLines data.a data.b data.c
    (points query)
  pure ⟨wire, decoded, inverses⟩

def pureIncrementBytes (body : Bytes) (query : Fin 22 -> Position)
    (data : Data (K := QM31Exact)) (alpha rho : QM31Exact) : Option Bytes := do
  let prepared ← pureOpenedPreparation body query data
  let opened := recordFold data prepared.decoded
    query prepared.inverses alpha
  pure (SameBodyAuthenticatedIncrement.canonicalBytes
    (SameBodyQueryClaim.increment (ringArithmetic (1/4 : QM31Exact)) rho opened))

/-! The transcript-only part after authenticated opening arithmetic.  Its
input is the verifier-computed canonical increment, not a prover message. -/
def laterBytesScript (incrementBytes : Bytes) (body : Bytes)
    (rhoDigest : Block) :
    Script (List UInt8) Block
      (Except InterleavedError LaterSuccess × Block) 202 :=
  bind (absorbScript rhoDigest 1 incrementBytes)
    fun afterIncrement =>
  bind (absorbScript afterIncrement 52
      (1 :: FSLiveLaterRelationSuffix.responseBytes body 1))
    fun afterResponse1 =>
  bind (FSNonzeroQM31.candidateScript afterResponse1)
    fun alpha1Draw =>
  match alpha1Draw.1 with
  | .error e => .done (.error (.alpha1 e), alpha1Draw.2)
  | .ok alpha1 =>
    bind (absorbScript alpha1Draw.2 52
        (2 :: FSLiveLaterRelationSuffix.responseBytes body 2))
      fun afterResponse2 =>
    bind (FSNonzeroQM31.candidateScript afterResponse2)
      fun alpha2Draw =>
    match alpha2Draw.1 with
    | .error e => .done (.error (.alpha2 e), alpha2Draw.2)
    | .ok alpha2 =>
      bind (absorbScript alpha2Draw.2 52
          (3 :: FSLiveLaterRelationSuffix.responseBytes body 3))
        fun afterResponse3 =>
      bind (FSNonzeroQM31.candidateScript afterResponse3)
        fun alpha3Draw =>
        .done (match alpha3Draw.1 with
          | .error e => (.error (.alpha3 e), alpha3Draw.2)
          | .ok alpha3 =>
            (.ok ⟨alpha1, alpha2, alpha3⟩, alpha3Draw.2))

/-! The actual post-rho order.  `selected22` performs the q22 Merkle calls;
the callback then uses the fixed rho digest (selected calls do not absorb) to
start the increment at profile label 1, followed by response1--3 and their
alpha challenges.  The pinned protocol name `73` is not the absorb label. -/

def interleavedSelectedSuffix (cuts : RootCuts)
    (positions : Fin 22 -> Position) (body : Bytes)
    (rhoDigest : Block)
    (data : Data (K := QM31Exact)) (alpha rho : QM31Exact) :
    Script (List UInt8) Block
      (Except InterleavedError InterleavedSuccess × Block) 1038 :=
  bind (m := 202) (selected22 cuts positions (encode body)) fun trace =>
    match pureIncrementBytes body positions data alpha rho with
    | none => .done (.error .openedPipeline, rhoDigest)
    | some incrementBytes =>
      bind (m := 0) (laterBytesScript incrementBytes body rhoDigest) fun later =>
        .done (match later.1 with
          | .error e => (.error e, later.2)
          | .ok success =>
            (.ok ⟨trace, success.alpha1, success.alpha2, success.alpha3⟩,
              later.2))

theorem interleaved_success_decomposes
    (cuts : RootCuts) (positions : Fin 22 -> Position) (body : Bytes)
    (rhoDigest : Block)
    (data : Data (K := QM31Exact)) (alpha rho : QM31Exact)
    (tape : Tape) (oracle : FSBoundedTranscript.Oracle)
    (result : Except InterleavedError InterleavedSuccess)
    (finalDigest : Block)
    (success :
      (run tape (interleavedSelectedSuffix cuts positions body rhoDigest
        data alpha rho) oracle).1 = some (result, finalDigest)) :
    pureIncrementBytes body positions data alpha rho = none ∨
      ∃ trace bytes,
        (run tape (selected22 cuts positions (encode body)) oracle).1 =
          some trace ∧
        pureIncrementBytes body positions data alpha rho = some bytes := by
  unfold interleavedSelectedSuffix at success
  rw [run_bind] at success
  cases pureRun : pureIncrementBytes body positions data alpha rho with
  | none => exact Or.inl rfl
  | some bytes =>
    right
    cases selectedRun :
        (run tape (selected22 cuts positions (encode body)) oracle).1 with
    | none => simp [selectedRun] at success
    | some trace => exact ⟨trace, bytes, rfl, rfl⟩

/-- An accepting interleaved suffix exposes the exact authenticated trace and
the exact verifier-computed increment.  Neither equality is a caller premise. -/
theorem interleaved_ok_constructs_selected_and_increment
    (cuts : RootCuts) (positions : Fin 22 -> Position) (body : Bytes)
    (rhoDigest : Block)
    (data : Data (K := QM31Exact)) (alpha rho : QM31Exact)
    (tape : Tape) (oracle : FSBoundedTranscript.Oracle)
    (output : InterleavedSuccess) (finalDigest : Block)
    (success :
      (run tape (interleavedSelectedSuffix cuts positions body rhoDigest
        data alpha rho) oracle).1 = some (.ok output, finalDigest)) :
    ∃ bytes,
      (run tape (selected22 cuts positions (encode body)) oracle).1 =
          some output.selectedTrace ∧
      pureIncrementBytes body positions data alpha rho = some bytes ∧
      (run tape (laterBytesScript bytes body rhoDigest)
        (run tape (selected22 cuts positions (encode body)) oracle).2).1 =
          some (.ok ⟨output.alpha1, output.alpha2, output.alpha3⟩,
            finalDigest) := by
  unfold interleavedSelectedSuffix at success
  rw [run_bind] at success
  cases selectedRun :
      (run tape (selected22 cuts positions (encode body)) oracle).1 with
  | none => simp [selectedRun] at success
  | some trace =>
      simp only [selectedRun] at success
      cases incrementRun : pureIncrementBytes body positions data alpha rho with
      | none => simp [incrementRun, run] at success
      | some bytes =>
          simp only [incrementRun, run_bind] at success
          cases laterRun :
              (run tape (laterBytesScript bytes body rhoDigest)
                (run tape (selected22 cuts positions (encode body)) oracle).2).1 with
          | none => simp [laterRun] at success
          | some later =>
              rcases later with ⟨laterResult, laterDigest⟩
              cases laterResult with
              | error e => simp [laterRun, run] at success
              | ok laterSuccess =>
                  simp [laterRun, run] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact ⟨bytes, rfl, rfl, laterRun⟩

#print axioms interleaved_success_decomposes
#print axioms interleaved_ok_constructs_selected_and_increment

end AspisV8Completion.FSInterleavedSelectedIncrementBoundary
