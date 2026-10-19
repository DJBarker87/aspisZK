import RawSemanticCheckedStepPolynomialAdapter
import RawSemanticPolynomialDegree28
import RawExtractedSemanticPolynomialWrappersV1
import RawExtractedSemanticValueLoopV1

set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev GenQM := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

def mainToGen (q : MainQM) : GenQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def genToMain (q : GenQM) : MainQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

theorem genQToProbe_mainToGen (q : MainQM) :
    AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe
      (mainToGen q) = mainToProbe q := rfl

theorem mainToGen_genToMain (q : GenQM) : mainToGen (genToMain q) = q := by
  cases q with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem mainToProbe_genToMain (q : GenQM) :
    mainToProbe (genToMain q) =
      AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe q := rfl

def mainArrayToGen (xs : Array MainQM 28#usize) : Array GenQM 28#usize :=
  ⟨xs.val.map mainToGen, by simpa using xs.property⟩

def mainAlphaArrayToGen (xs : Array MainQM 10#usize) : Array GenQM 10#usize :=
  ⟨xs.val.map mainToGen, by simpa using xs.property⟩

def genResultToMain : Result GenQM → Result MainQM
  | .ok q => .ok (genToMain q)
  | .fail e => .fail e
  | .div => .div

def generatedMainBoundary (coefficients : Array MainQM 28#usize) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry
    (mainArrayToGen coefficients))

def generatedMainValue (coefficients : Array MainQM 28#usize)
    (alpha : Array MainQM 10#usize) (round : Usize) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
    (mainArrayToGen coefficients) (mainAlphaArrayToGen alpha) round)

def generatedRoundBoundaries
    (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error)) :
    AspisR1PublicPreparation.RoundModel.Boundaries :=
  { decode := decodeMain
    boundary := generatedMainBoundary
    value := generatedMainValue }

theorem generated_coefficients_eq_probe (coefficients : Array MainQM 28#usize) :
    AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients
      (mainArrayToGen coefficients) =
      (mainArrayToProbe coefficients).val.map AspisR1.ExtractedMaskQM31Exact.decode := by
  simp [AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients,
    mainArrayToGen, mainToGen, mainArrayToProbe,
    AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe,
    AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genCToProbe, mainToProbe]

theorem index_success_option {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (x : α) (h : Array.index_usize a i = .ok x) : a.val[i.val]? = some x := by
  unfold Array.index_usize at h
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some y => Result.ok y) = Result.ok x at h
  cases hi : a.val[i.val]? with
  | none =>
      rw [hi] at h
      cases h
  | some y =>
      rw [hi] at h
      change Result.ok y = Result.ok x at h
      have heq : y = x := Result.ok.inj h
      exact congrArg some heq

theorem index_success_bound {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (x : α) (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hopt := index_success_option a i x h
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a.val[i.val]? = none :=
      (List.getElem?_eq_none_iff).2 (Nat.le_of_not_gt hnot)
    rw [hnone] at hopt
    cases hopt
  simpa [a.property] using hlen

theorem generated_boundary_refines (coefficients : Array MainQM 28#usize)
    (hcoeff : ∀ x ∈ (mainArrayToProbe coefficients).val, Canonical x) :
    ∃ out,
      generatedMainBoundary coefficients = .ok out ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe out) =
        (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 := by
  have hp : ∀ i : Nat, (hi : i < 28) →
      Canonical (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe
        ((mainArrayToGen coefficients).val[i]'(by simpa [mainArrayToGen,
          coefficients.property] using hi))) := by
    intro i hi
    have hrew : AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe
        ((mainArrayToGen coefficients).val[i]'(by
          simpa [mainArrayToGen, coefficients.property] using hi)) =
        mainToProbe (coefficients.val[i]'(by simpa [coefficients.property] using hi)) := by
      simp [mainArrayToGen, mainToGen,
        AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe,
        AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genCToProbe, mainToProbe]
    rw [hrew]
    apply hcoeff
    have hiMem : coefficients.val[i]'(by
        simpa [coefficients.property] using hi) ∈ coefficients.val :=
      List.getElem_mem (by simpa [coefficients.property] using hi)
    have hmemMap : mainToProbe (coefficients.val[i]'(by
        simpa [coefficients.property] using hi)) ∈ coefficients.val.map mainToProbe :=
      List.mem_map.mpr ⟨_, hiMem, rfl⟩
    simpa [mainArrayToProbe] using hmemMap
  obtain ⟨out, hrun, hcanonical, hpoly⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1.semantic_boundary_refines_polynomial_endpoints
      (mainArrayToGen coefficients) hp
  have hcoeffeq := generated_coefficients_eq_probe coefficients
  have hcoeffeqV :
      AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.coefficients
          (mainArrayToGen coefficients) =
        (mainArrayToProbe coefficients).val.map AspisR1.ExtractedMaskQM31Exact.decode := by
    simpa [AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.coefficients,
      AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients] using hcoeffeq
  refine ⟨genToMain out, ?_, ?_⟩
  · change genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry
        (mainArrayToGen coefficients)) = .ok (genToMain out)
    rw [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry, hrun]
    rfl
  · rw [mainToProbe_genToMain]
    rw [hcoeffeq] at hpoly
    simpa [exactPolynomial] using hpoly

theorem checkedStep_polynomial_equations
    {H : Type} (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8)
    (hstep : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
      (generatedRoundBoundaries decodeMain) D pre before after round row)
    (hcanonicalCoeff : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize),
      decodeMain 28#usize record 0#usize = .ok (.Ok coefficients) →
      ∀ x ∈ (mainArrayToProbe coefficients).val, Canonical x)
    (hcanonicalChallenge : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (q : MainQM),
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        before.2.2 record = .ok (.Ok q, after.2.2) → Canonical (mainToProbe q))
    (hindex : ∀ q : MainQM,
      Array.index_usize (before.2.1.set round q) round = .ok q) :
    ∃ record coefficients q,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
      decodeMain 28#usize record 0#usize = .ok (.Ok coefficients) ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        before.2.2 record = .ok (.Ok q, after.2.2) ∧
      after.2.1 = before.2.1.set round q ∧
      (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
        (exactPolynomial coefficients).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
  change ∃ record coefficients boundary q, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hstep
  rcases hstep with ⟨record, coefficients, boundary, q,
    hrecord, hdecode, hboundary, hneq, hboundaryEq, hsemantic, hset, hvalue⟩
  have hcoeff := hcanonicalCoeff record coefficients hdecode
  obtain ⟨mappedBoundary, hboundaryRun, hboundaryEval⟩ :=
    generated_boundary_refines coefficients hcoeff
  have hboundaryRun' : generatedMainBoundary coefficients = .ok boundary := by
    simpa [generatedRoundBoundaries] using hboundary
  have hboundaryEq' : mappedBoundary = boundary :=
    Result.ok.inj (hboundaryRun.symm.trans hboundaryRun')
  have hqCanonical := hcanonicalChallenge record q hsemantic
  have hidx := hindex q
  have hroundBound : round.val < 10 := by
    have hb := index_success_bound (before.2.1.set round q) round q hidx
    simpa [(before.2.1.set round q).property] using hb
  have hselectedOpt := index_success_option (before.2.1.set round q) round q hidx
  have hchallenge :
      (mainAlphaArrayToGen (before.2.1.set round q)).val[round.val]'(by
        simpa [(before.2.1.set round q).property] using hroundBound) = mainToGen q := by
    simp only [mainAlphaArrayToGen, List.getElem_map]
    have hget := List.getElem?_eq_getElem
      (show round.val < (before.2.1.set round q).val.length by
        simpa [(before.2.1.set round q).property] using hroundBound)
    rw [hget] at hselectedOpt
    exact congrArg mainToGen (Option.some.inj hselectedOpt)
  have hcoeffeq := generated_coefficients_eq_probe coefficients
  have hcoeffeqV :
      AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.coefficients
          (mainArrayToGen coefficients) =
        (mainArrayToProbe coefficients).val.map AspisR1.ExtractedMaskQM31Exact.decode := by
    simpa [AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.coefficients,
      AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients] using hcoeffeq
  obtain ⟨mappedValue, hvalueRun, hvalueEval⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
      (mainArrayToGen coefficients) (mainAlphaArrayToGen (before.2.1.set round q)) round
      hroundBound (by
        change Canonical (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe
          ((mainAlphaArrayToGen (before.2.1.set round q)).val[round.val]'(by
            simpa [(before.2.1.set round q).property] using hroundBound)))
        rw [hchallenge, genQToProbe_mainToGen]
        exact hqCanonical) (by
        intro i hi
        have hrew : AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe
            ((mainArrayToGen coefficients).val[i]'(by
              simpa [mainArrayToGen, coefficients.property] using hi)) =
            mainToProbe (coefficients.val[i]'(by simpa [coefficients.property] using hi)) := by
          simp [mainArrayToGen, mainToGen,
            AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe,
            AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genCToProbe, mainToProbe]
        rw [hrew]
        apply hcoeff
        have hiMem : coefficients.val[i]'(by
            simpa [coefficients.property] using hi) ∈ coefficients.val :=
          List.getElem_mem (by simpa [coefficients.property] using hi)
        have hmemMap : mainToProbe (coefficients.val[i]'(by
            simpa [coefficients.property] using hi)) ∈ coefficients.val.map mainToProbe :=
          List.mem_map.mpr ⟨_, hiMem, rfl⟩
        simpa [mainArrayToProbe] using hmemMap)
  have hentry : AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
      (mainArrayToGen coefficients) (mainAlphaArrayToGen (before.2.1.set round q)) round =
      .ok (mainToGen after.1) := by
    have hmain : generatedMainValue coefficients (before.2.1.set round q) round = .ok after.1 := by
      rw [hset] at hvalue
      simpa [generatedRoundBoundaries] using hvalue
    cases hraw : AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
        (mainArrayToGen coefficients) (mainAlphaArrayToGen (before.2.1.set round q)) round with
    | ok x =>
        have hx : genToMain x = after.1 := by
          simpa [generatedMainValue, genResultToMain, hraw] using hmain
        have hxi : x = mainToGen after.1 := by
          have := congrArg mainToGen hx
          rw [mainToGen_genToMain] at this
          exact this
        simpa [hraw, hxi]
    | fail e => simp [generatedMainValue, genResultToMain, hraw] at hmain
    | div => simp [generatedMainValue, genResultToMain, hraw] at hmain
  have hvalueRun' : AspisR1SemanticCallExtraction.r1_semantic.semantic_value
      (mainArrayToGen coefficients) (mainAlphaArrayToGen (before.2.1.set round q)) round =
      .ok (mainToGen after.1) := by
    simpa [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry] using hentry
  have hmapvalue : mappedValue = mainToGen after.1 :=
    Result.ok.inj (hvalueRun.symm.trans hvalueRun')
  refine ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset, ?_, ?_⟩
  · calc
      (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
          AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe mappedBoundary) := hboundaryEval.symm
      _ = AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe boundary) := by rw [hboundaryEq']
      _ = AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) := by rw [hboundaryEq]
  · calc
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
          AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe mappedValue) := by
              rw [← genQToProbe_mainToGen, ← hmapvalue]
      _ = (exactPolynomial coefficients).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
            unfold exactPolynomial
            rw [← hcoeffeqV]
            have hpoint := congrArg
              (fun x => AspisR1.ExtractedMaskQM31Exact.decode
                (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe x))
              hchallenge
            rw [genQToProbe_mainToGen] at hpoint
            rw [← hpoint]
            exact hvalueEval.2

#print axioms generated_boundary_refines
#print axioms checkedStep_polynomial_equations
end AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter
