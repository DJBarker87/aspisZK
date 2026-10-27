import RPt_FIq_S_ExtractedSemanticRoundsCheckedTrace
import ExtractedMaskQM31Exact
import RPt_JFv_RawExtractedSemanticQM31Ops

/-! A structural adapter from the public-preparation QM31 record to the exact
field.rs extraction reused by the arithmetic-probe proofs.  The public
preparation Aeneas owner supplies the QM31 record type but treats the imported
aspis-core add/mul methods as external; this file therefore names the mapped
source operations explicitly and does not claim that RoundModel.Boundaries is
already instantiated by them. -/
set_option autoImplicit false

namespace AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter

open Aeneas Aeneas.Std Result

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev ProbeQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

/-- Rewrap the same four U32 coordinates in the exact field.rs extraction. -/
def mainToProbe (x : MainQM) : ProbeQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

/-- Inverse coordinate rewrapping into the public-preparation field type. -/
def probeToMain (x : ProbeQM) : MainQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

@[simp] theorem mainToProbe_probeToMain (x : ProbeQM) :
    mainToProbe (probeToMain x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

@[simp] theorem probeToMain_mainToProbe (x : MainQM) :
    probeToMain (mainToProbe x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem main_coordinates_canonical_iff (x : MainQM) :
    Canonical (mainToProbe x) ↔
      x.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P := by
  change
    (x.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P) ∧
    (x.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P) ↔ _
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩

/-- Lift a probe Result through the inverse coordinate isomorphism. -/
def probeResultToMain : Result ProbeQM → Result MainQM
  | .ok x => .ok (probeToMain x)
  | .fail e => .fail e
  | .div => .div

/-- The source-shaped add operation on public-preparation coordinates, using
the byte-pinned field.rs extraction as the operation body. -/
def extractedMainAdd (x y : MainQM) : Result MainQM :=
  probeResultToMain
    (AspisR1SelectedMaskProbe.field.QM31.add (mainToProbe x) (mainToProbe y))

/-- The source-shaped multiply operation on public-preparation coordinates,
using the same pinned field.rs extraction. -/
def extractedMainMul (x y : MainQM) : Result MainQM :=
  probeResultToMain
    (AspisR1SelectedMaskProbe.field.QM31.mul (mainToProbe x) (mainToProbe y))

theorem extractedMainAdd_refines (x y : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y)) :
    ∃ z, extractedMainAdd x y = .ok z ∧ Canonical (mainToProbe z) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe z) =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x) +
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe y) := by
  obtain ⟨z, hz, hcanonical, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      (mainToProbe x) (mainToProbe y) hx hy
  refine ⟨probeToMain z, ?_, ?_, ?_⟩
  · simp [extractedMainAdd, probeResultToMain, hz]
  · simpa using hcanonical
  · simpa using hdecode

theorem extractedMainMul_refines (x y : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y)) :
    ∃ z, extractedMainMul x y = .ok z ∧ Canonical (mainToProbe z) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe z) =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x) *
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe y) := by
  obtain ⟨z, hz, hcanonical, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact
      (mainToProbe x) (mainToProbe y) hx hy
  refine ⟨probeToMain z, ?_, ?_, ?_⟩
  · simp [extractedMainMul, probeResultToMain, hz]
  · simpa using hcanonical
  · simpa using hdecode

/-- Rewrap the fixed semantic coefficient array pointwise. -/
def mainArrayToProbe (coefficients : Array MainQM 28#usize) :
    Array ProbeQM 28#usize :=
  ⟨coefficients.val.map mainToProbe, by simpa using coefficients.property⟩

/-- Main-owner boundary adapter: the body is the exact pinned field.rs
extraction applied to the public-preparation coordinates. -/
def extractedMainBoundary (coefficients : Array MainQM 28#usize) : Result MainQM :=
  probeResultToMain
    (AspisR1PublicPreparation.RawExtractedSemanticQM31Ops.semanticBoundaryArrayResult
      (mainArrayToProbe coefficients))

theorem extractedMainBoundary_refines (coefficients : Array MainQM 28#usize)
    (hcoefficients : ∀ x ∈ (mainArrayToProbe coefficients).v, Canonical x) :
    ∃ boundary, extractedMainBoundary coefficients = .ok boundary ∧
      Canonical (mainToProbe boundary) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe boundary) =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          ((mainArrayToProbe coefficients).v.map
            AspisR1.ExtractedMaskQM31Exact.decode)).eval 0 +
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          ((mainArrayToProbe coefficients).v.map
            AspisR1.ExtractedMaskQM31Exact.decode)).eval 1 := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticQM31Ops.semanticBoundaryArrayResult_eq_polynomial_endpoints
      (mainArrayToProbe coefficients) hcoefficients
  refine ⟨probeToMain out, ?_, ?_, ?_⟩
  · simp [extractedMainBoundary, probeResultToMain, hout]
  · simpa using hcanonical
  · simpa using hvalue

/-- Main-owner value adapter: reverse Horner over the 28 source coefficients,
using the same exact field.rs extraction for each add/multiply. -/
def extractedMainValue (alpha : MainQM) (coefficients : Array MainQM 28#usize) :
    Result MainQM :=
  probeResultToMain
    (AspisR1PublicPreparation.RawExtractedSemanticQM31Ops.hornerArrayResult
      (mainToProbe alpha) (mainArrayToProbe coefficients))

theorem extractedMainValue_refines (alpha : MainQM)
    (coefficients : Array MainQM 28#usize)
    (halpha : Canonical (mainToProbe alpha))
    (hcoefficients : ∀ x ∈ (mainArrayToProbe coefficients).v, Canonical x) :
    ∃ value, extractedMainValue alpha coefficients = .ok value ∧
      Canonical (mainToProbe value) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe value) =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          ((mainArrayToProbe coefficients).v.map
            AspisR1.ExtractedMaskQM31Exact.decode)).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe alpha)) := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticQM31Ops.hornerArrayResult_refines_polynomial_eval
      (mainToProbe alpha) (mainArrayToProbe coefficients) halpha hcoefficients
  refine ⟨probeToMain out, ?_, ?_, ?_⟩
  · simp [extractedMainValue, probeResultToMain, hout]
  · simpa using hcanonical
  · simpa using hvalue


/-- Value operation at the actual challenge coordinate stored in the ten-entry
round array.  The enclosing Aeneas model's index lookup is retained explicitly. -/
def extractedMainValueAt (coefficients : Array MainQM 28#usize)
    (alpha : Array MainQM 10#usize) (round : Std.Usize) : Result MainQM := do
  let challenge ← Array.index_usize alpha round
  extractedMainValue challenge coefficients

theorem extractedMainValueAt_refines (coefficients : Array MainQM 28#usize)
    (alpha : Array MainQM 10#usize) (round : Std.Usize) (challenge : MainQM)
    (hindex : Array.index_usize alpha round = .ok challenge)
    (hchallenge : Canonical (mainToProbe challenge))
    (hcoefficients : ∀ x ∈ (mainArrayToProbe coefficients).v, Canonical x) :
    ∃ value, extractedMainValueAt coefficients alpha round = .ok value ∧
      Canonical (mainToProbe value) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe value) =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          ((mainArrayToProbe coefficients).v.map
            AspisR1.ExtractedMaskQM31Exact.decode)).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe challenge)) := by
  obtain ⟨value, hvalue, hcanonical, heval⟩ :=
    extractedMainValue_refines challenge coefficients hchallenge hcoefficients
  refine ⟨value, ?_, hcanonical, heval⟩
  simp [extractedMainValueAt, hindex, hvalue]


/-- Concrete semantic-round model constructor.  `decodeMain` is the exact row
parser supplied by the caller; boundary/value are the coordinate-transported
field.rs fold and Horner functions above. -/
def mainRoundBoundaries
    (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error)) :
    AspisR1PublicPreparation.RoundModel.Boundaries :=
  { decode := decodeMain
    boundary := extractedMainBoundary
    value := extractedMainValueAt }

@[simp] theorem mainRoundBoundaries_decode (decodeMain) :
    (mainRoundBoundaries decodeMain).decode = decodeMain := rfl

@[simp] theorem mainRoundBoundaries_boundary (decodeMain)
    (coefficients : Array MainQM 28#usize) :
    (mainRoundBoundaries decodeMain).boundary coefficients =
      extractedMainBoundary coefficients := rfl

@[simp] theorem mainRoundBoundaries_value (decodeMain)
    (coefficients : Array MainQM 28#usize) (alpha : Array MainQM 10#usize)
    (round : Std.Usize) :
    (mainRoundBoundaries decodeMain).value coefficients alpha round =
      extractedMainValueAt coefficients alpha round := rfl

#print axioms mainToProbe_probeToMain
#print axioms probeToMain_mainToProbe
#print axioms main_coordinates_canonical_iff
#print axioms extractedMainAdd_refines
#print axioms extractedMainMul_refines
#print axioms extractedMainBoundary_refines
#print axioms extractedMainValue_refines
#print axioms extractedMainValueAt_refines
#print axioms mainRoundBoundaries_decode
#print axioms mainRoundBoundaries_boundary
#print axioms mainRoundBoundaries_value

end AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
