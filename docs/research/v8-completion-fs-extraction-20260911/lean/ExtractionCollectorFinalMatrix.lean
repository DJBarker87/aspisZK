import ExtractionCollectorSource
import FSAuthenticatedInterleavedPrefixMiddle
import SelectedMiddleFourAlpha
import Gamma29Reconstruction

/-!
# Permitted-access final-value matrix

This is the deterministic bridge from checked replay records to their
body-derived final values.  Each replay carries its own submitted body:
challenge-dependent suffix messages must not be frozen across forks.  A
later collector theorem must construct these records with one shared
authenticated commitment prefix.

The source middle success contains `functionalRun`.  Its existing
`fromInputs_provenance` theorem therefore supplies the successful canonical
fixed-field parse of that same body.  `final256` is defined from those parsed
fields using the canonical fixed final-field projection.

No witness, full-word input, candidate, `RecoveredHigh` oracle, or opening
request is used by this bridge.
-/
set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.ExtractionCollectorFinalMatrix

open ExtractionCollectorSource
open FSAuthenticatedInterleavedPrefixMiddle
open FSLiveSourceFunctionalMiddle
open SameBodyFunctionalProducerSource
open SameBodyRelation
open AspisV8.SameBodySequentialCodec

noncomputable section

abbrev K := FSNonzeroQM31.K
abbrev Bytes := List UInt8
abbrev Final := SameBodyRelation.Final K
abbrev WholeRecord (body : Bytes) (z : Fin 10 → K) :=
  FSAuthenticatedInterleavedPrefixMiddle.Record body z

/-- One checked replay and the exact body consumed by that replay.  The body
is existential data of the record, rather than a single body fixed for the
whole 29-by-4 matrix. -/
structure ReplayRecord (z : Fin 10 → K) where
  body : Bytes
  run : WholeRecord body z

def gammaOf {z : Fin 10 → K} (record : ReplayRecord z) : K :=
  record.run.gamma

def alphaOf {z : Fin 10 → K} (record : ReplayRecord z) : K :=
  record.run.middle.middle.alpha0

theorem parser_values {body : Bytes} {z : Fin 10 → K}
    (record : WholeRecord body z) :
    ∃ values, fields (body.map UInt8.toFin) = some values := by
  obtain ⟨values, bodyData, _fields, _correct, _description, _claim⟩ :=
    fromInputs_provenance record.out record.gamma record.middle.middle.kappa
      body z record.middle.functional record.middle.functionalRun
  exact ⟨values, _fields⟩

/-- Canonical final-256 values parsed from the same body that produced the
successful functional middle. -/
noncomputable def final256 {body : Bytes} {z : Fin 10 → K}
    (record : WholeRecord body z) : Final :=
  SameBodyRelation.finalValues
    (wordOfValues (Classical.choose (parser_values record)))

noncomputable def replayFinal256 {z : Fin 10 → K}
    (record : ReplayRecord z) : Final :=
  final256 record.run

theorem final256_parser {body : Bytes} {z : Fin 10 → K}
    (record : WholeRecord body z) :
    fields (body.map UInt8.toFin) =
      some (Classical.choose (parser_values record)) :=
  Classical.choose_spec (parser_values record)

/-- The canonical final projection is literally the fixed body-field window
441..696, expressed through the parsed 697-field list. -/
theorem final256_fixed_body {body : Bytes} {z : Fin 10 → K}
    (record : WholeRecord body z) :
    final256 record =
      fun j => (Classical.choose (parser_values record)).getD (441 + j.val) 0 := by
  funext j
  simp [final256, SameBodyRelation.finalValues, SameBodyRelation.finalIndex,
    SameBodyFunctionalProducerSource.wordOfValues]

/-- The 29-by-4 final values selected from supplied `.checked` replay records.
The collector source must still prove that those records came from legal
successful replays.  The only final projection is the canonical `final256`
above. -/
def finalValuesMatrix {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes) :
    Fin 29 → Fin 4 → Fin 256 → K :=
  fun row column => replayFinal256 (complete.matrix row column)

theorem finalValuesMatrix_returned {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    finalValuesMatrix labels outcomes complete row column =
      replayFinal256 (complete.matrix row column) := by
  rfl

theorem finalValuesMatrix_labels {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    gammaOf (complete.matrix row column) = labels.gamma row ∧
      alphaOf (complete.matrix row column) = labels.alpha row column := by
  exact ⟨complete.gamma_eq row column, complete.alpha_eq row column⟩

/-! ## Value-keyed four-alpha adapter -/

/-- The actual alpha nodes for one scheduled gamma row. -/
def alphaNodes (labels : MatrixLabels K K)
    (row : Fin 29) : Finset K :=
  Finset.univ.image (labels.alpha row)

theorem alphaNodes_card (labels : MatrixLabels K K)
    (row : Fin 29) : (alphaNodes labels row).card = 4 := by
  classical
  unfold alphaNodes
  rw [Finset.card_image_of_injective _ (labels.alpha_injective row)]
  simp

/-- Lookup of a final vector by alpha value.  The sum is finite and uses only
the four returned matrix cells; injectivity makes it one-hot on scheduled
labels. -/
def alphaFinal {z : Fin 10 → K} {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) (alpha : K) : Final :=
  fun j => ∑ column : Fin 4,
    if labels.alpha row column = alpha then
      finalValuesMatrix labels outcomes complete row column j else 0

theorem alphaFinal_at_label {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    alphaFinal labels outcomes complete row (labels.alpha row column) =
      finalValuesMatrix labels outcomes complete row column := by
  classical
  funext j
  unfold alphaFinal
  rw [Finset.sum_eq_single column]
  · simp
  · intro other _member different
    have distinct : labels.alpha row other ≠ labels.alpha row column := by
      intro equal
      exact different (labels.alpha_injective row equal)
    simp [distinct]
  · intro absent
    exact (absent (Finset.mem_univ column)).elim

theorem alphaFinal_on_nodes {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) :
    ∀ alpha ∈ alphaNodes labels row,
      ∃ column, alpha = labels.alpha row column ∧
        alphaFinal labels outcomes complete row alpha =
          finalValuesMatrix labels outcomes complete row column := by
  intro alpha member
  rcases Finset.mem_image.mp member with ⟨column, _member, rfl⟩
  exact ⟨column, rfl, alphaFinal_at_label labels outcomes complete row column⟩

/-! ## Deterministic gamma-layer adapter -/

/-- The actual gamma nodes represented by the scheduled matrix rows. -/
def gammaNodes (labels : MatrixLabels K K) : Finset K :=
  Finset.univ.image labels.gamma

theorem gammaNodes_card (labels : MatrixLabels K K) :
    (gammaNodes labels).card = 29 := by
  classical
  unfold gammaNodes
  rw [Finset.card_image_of_injective _ labels.gamma_injective]
  simp

/-- Four-alpha reconstruction for one matrix row. -/
def reconstructedRow {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) : Fin 1024 → K :=
  AspisV8.SelectedMiddleFourAlpha.Generic.reconstruct
    (alphaNodes labels row) (alphaFinal labels outcomes complete row)

/-- Gamma-keyed lookup of the reconstructed row values. -/
def gammaCandidate {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (gamma : K) : Fin 1024 → K :=
  fun i => ∑ row : Fin 29,
    if labels.gamma row = gamma then reconstructedRow labels outcomes complete row i
    else 0

theorem gammaCandidate_at_label {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) :
    gammaCandidate labels outcomes complete (labels.gamma row) =
      reconstructedRow labels outcomes complete row := by
  classical
  funext i
  unfold gammaCandidate
  rw [Finset.sum_eq_single row]
  · simp
  · intro other _member different
    have distinct : labels.gamma other ≠ labels.gamma row := by
      intro equal
      exact different (labels.gamma_injective equal)
    simp [distinct]
  · intro absent
    exact (absent (Finset.mem_univ row)).elim

theorem gammaCandidate_on_nodes {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (gamma : K) (member : gamma ∈ gammaNodes labels) :
    ∃ row, gamma = labels.gamma row ∧
      gammaCandidate labels outcomes complete gamma =
        reconstructedRow labels outcomes complete row := by
  rcases Finset.mem_image.mp member with ⟨row, _member, rfl⟩
  exact ⟨row, rfl, gammaCandidate_at_label labels outcomes complete row⟩

/-- Deterministic 29-row tuple from the released interpolation constructor. -/
def reconstructedTuple {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes) :
    Fin 29 → Fin 1024 → K :=
  AspisV8.Gamma29Reconstruction.reconstructed (gammaNodes labels)
    (gammaCandidate labels outcomes complete)

theorem reconstructedTuple_at_node {z : Fin 10 → K}
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : List (AttemptOutcome (ReplayRecord z)
      RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes)
    (row : Fin 29) :
    AspisV8.ClaimTransport.batch (labels.gamma row)
      (reconstructedTuple labels outcomes complete) =
      gammaCandidate labels outcomes complete (labels.gamma row) := by
  apply AspisV8.Gamma29Reconstruction.nodal_reconstruction
    (gammaNodes labels) (gammaCandidate labels outcomes complete)
    (gammaNodes_card labels)
  exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩

#print axioms parser_values
#print axioms final256_parser
#print axioms final256_fixed_body
#print axioms finalValuesMatrix_returned
#print axioms finalValuesMatrix_labels
#print axioms alphaNodes_card
#print axioms alphaFinal_at_label
#print axioms alphaFinal_on_nodes
#print axioms gammaNodes_card
#print axioms gammaCandidate_at_label
#print axioms gammaCandidate_on_nodes
#print axioms reconstructedTuple_at_node

end
end AspisV8Completion.ExtractionCollectorFinalMatrix
