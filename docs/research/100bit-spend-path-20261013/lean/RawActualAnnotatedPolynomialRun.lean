import RawActualEnrichedSemanticRun
import RawGenericPolynomialSumcheckChain

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter
open AspisR1PublicPreparation.RawActualSemanticRoundCanonicality
open AspisR1PublicPreparation.RawActualEnrichedSemanticRun
open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain

abbrev MainQM := AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM
abbrev E := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Outcome (H : Type) := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome H
abbrev DecodeMain (x : MainQM) : E :=
  AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x)

def polynomialOf (coefficients : Array MainQM 28#usize) : Polynomial E :=
  exactPolynomial coefficients

def challengeOf (q : MainQM) : E := DecodeMain q

/-- One annotated reached source step. The same record, coefficient array and
challenge are used for the decoder result, semantic call, polynomial equations,
and the retained `CheckedStep`; no unrelated list entry can be paired with a
successful run. -/
structure RoundEvidence {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) where
  round : Usize
  row : U8
  beforeState : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome H
  afterState : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome H
  sourceStep : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
    actualRoundBoundaries D pre beforeState afterState round row
  record : AspisR1PublicPreparation.r1_wire.ValidatedRecord
  coefficients : Array MainQM 28#usize
  q : MainQM
  recordOk : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row =
    .ok (.Ok record)
  decodeOk : AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
    28#usize record 0#usize = .ok (.Ok coefficients)
  semanticOk : AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
    D beforeState.2.2 record = .ok (.Ok q, afterState.2.2)
  alphaSet : afterState.2.1 = beforeState.2.1.set round q
  boundary : (polynomialOf coefficients).eval 0 +
      (polynomialOf coefficients).eval 1 = DecodeMain beforeState.1
  value : DecodeMain afterState.1 =
      (polynomialOf coefficients).eval (DecodeMain q)
  degree : (polynomialOf coefficients).natDegree ≤ 27

def pairOf {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (entry : RoundEvidence D pre) : Polynomial E × E :=
  (polynomialOf entry.coefficients, challengeOf entry.q)

/-- An ordered list of per-round evidence, indexed both by the concrete event
schedule and the before/after source states. -/
inductive AnnotatedRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) :
    List (Usize × U8) → Outcome H → Outcome H →
    List (RoundEvidence D pre) → Prop
  | nil (out : Outcome H) : AnnotatedRun D pre [] out out []
  | cons {entry : RoundEvidence D pre} {events : List (Usize × U8)}
      {final : Outcome H} {entries : List (RoundEvidence D pre)}
      (tail : AnnotatedRun D pre events entry.afterState final entries) :
      AnnotatedRun D pre ((entry.round, entry.row) :: events)
        entry.beforeState final (entry :: entries)

/-- Any enriched trace produced by the actual checked helper can be represented
as an annotated list whose entry fields retain that trace's precise witnesses. -/
theorem annotate_actual_run {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (hrun : Run D pre events initial final) :
    ∃ entries : List (RoundEvidence D pre),
      AnnotatedRun D pre events initial final entries := by
  induction hrun with
  | nil out => exact ⟨[], .nil out⟩
  | @cons round row rest before mid after sourceStep polynomialStep tail ih =>
      rcases polynomialStep with
        ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset,
          hboundary, hvalue, hdegree⟩
      rcases ih with ⟨entries, htail⟩
      let entry : RoundEvidence D pre :=
        ⟨round, row, before, mid, sourceStep, record, coefficients, q,
          hrecord, hdecode, hsemantic, hset, hboundary, hvalue, hdegree⟩
      refine ⟨entry :: entries, ?_⟩
      change AnnotatedRun D pre ((entry.round, entry.row) :: rest)
        entry.beforeState after (entry :: entries)
      exact .cons htail

/-- The list selected by an annotated actual trace satisfies the algebraic
sumcheck chain, with exact list correspondence through `pairOf`. -/
theorem annotatedRun_to_chain {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre events initial final entries) :
    Chain (DecodeMain initial.1) (DecodeMain final.1)
      (entries.map (pairOf D pre)) := by
  induction hrun with
  | nil out => exact .nil _
  | @cons entry events final entries tail ih =>
      simp only [List.map_cons, pairOf, polynomialOf, challengeOf]
      exact .cons entry.degree entry.boundary entry.value ih

/-- Successful actual rounds yield both the reached annotated witnesses and a
chain whose entries are definitionally built from those witnesses. The public
alpha output remains connected to the actual semantic-call list. -/
theorem rounds_success_actual_annotated {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self afterRounds : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : MainQM)
    (alpha : Array MainQM 10#usize)
    (hrounds : AspisR1PublicPreparation.RoundModel.rounds
      actualRoundBoundaries D pre self = .ok (.Ok (running, alpha, afterRounds))) :
    ∃ record decoded initial qs entries,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 14#u8 =
        .ok (.Ok record) ∧
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
        1#usize record 0#usize = .ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize = .ok initial ∧
      AspisR1PublicPreparation.BeginCalls.SemanticRun D pre
        AspisR1PublicPreparation.RoundCalls.rows self afterRounds qs ∧
      qs = alpha.val ∧
      AnnotatedRun D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO, self)
        (running, alpha, afterRounds) entries ∧
      Chain (DecodeMain initial)
        (DecodeMain running) (entries.map (pairOf D pre)) := by
  obtain ⟨record, decoded, initial, qs, hrecord, hdecode, hinitial,
      hsemanticRun, hqs, henriched⟩ :=
    rounds_success_actual_enriched D pre self afterRounds running alpha hrounds
  obtain ⟨entries, hannotated⟩ :=
    annotate_actual_run D pre _ _ _ henriched
  have hchain := annotatedRun_to_chain D pre _ _ _ entries hannotated
  exact ⟨record, decoded, initial, qs, entries, hrecord, hdecode, hinitial,
    hsemanticRun, hqs, hannotated, hchain⟩

#print axioms annotate_actual_run
#print axioms annotatedRun_to_chain
#print axioms rounds_success_actual_annotated
end AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
end
