import R0P.Zerocheck
import R0P.PositivityChain
import R0P.Semantics
import R0P.Occupancy
import R0P.Asset
import R0P.Extraction

/-! Lead: the SEM assembly.

`semantic_sound` takes the terminal's acceptance (through `Zerocheck.compose`)
to the production families' `Holds`, the copy challenge family, and, through
the LogUp step, `CopyLinkBalance`; from there `positivity_of_balance` (with
the proposal's positivity lane as a labelled hypothesis, Finding 1) and, once
G9 lands, `InputNoteExtracted`.

Two obligations are named rather than imported, so this file compiles before
they exist and closes by instantiation:
- `LaneInterface`: G11′'s `lanes_zero_iff_holds` for the production lane map
  (θ order Poseidon 0–3, semantic 4–27, copy 28);
- `LogUpStep`: the deterministic LogUp assembly (G5–G7 with the χ/λ bad
  sets of the ledger). -/
set_option autoImplicit false
namespace R0P
open Sumcheck

variable {K : Type} [Field K]

/-- The production families, as `lanes_zero_iff_holds` lists them. -/
def ProductionHolds (pub : Public K) (lam chi : K) (t : Trace K) : Prop :=
  Holds valueFamily pub t ∧ Holds occupancyFamily pub t ∧ Holds assetFamily pub t ∧
  Holds scheduleFamily pub t ∧ Holds pathFamily pub t ∧ Holds digestFamily pub t ∧
  Holds poseidonScalarFamily pub t ∧ CHolds copyFamily pub lam chi t

/-- G11′: the lane map separates into the production families. -/
def LaneInterface (pub : Public K) (lam chi : K) (t : Trace K)
    (laneOf : Fin 29 → (Fin 10 → Bool) → K) : Prop :=
  (∀ i b, laneOf i b = 0) ↔ ProductionHolds pub lam chi t

/-- The LogUp step: the copy challenge family with both helper sums zero,
for (λ, χ) outside the ledger's tupleCompression/activePole/copyChi bad
sets, gives link balance. `BadLogUp` is that bad set, to be defined with
G5–G7; here it is a parameter. -/
def LogUpStep (pub : Public K) (t : Trace K) (BadLogUp : K → K → Prop)
    (H1 inact : (Fin 10 → Bool) → K) : Prop :=
  ∀ lam chi, ¬ BadLogUp lam chi → CHolds copyFamily pub lam chi t →
    bsumB 10 H1 = 0 → bsumB 10 inact = 0 → CopyLinkBalance pub t

/-- Semantic soundness for one candidate trace: acceptance outside the
ledger's bad sets yields every production family and link balance. -/
theorem semantic_sound (pub : Public K) (t : Trace K) (lam chi θ μ : K) (zc : Fin 10 → K)
    (laneOf : Fin 29 → (Fin 10 → Bool) → K) (hlane : LaneInterface pub lam chi t laneOf)
    (BadLogUp : K → K → Prop) (H1 inact : (Fin 10 → Bool) → K)
    (hlogup : LogUpStep pub t BadLogUp H1 inact) (hlc : ¬ BadLogUp lam chi)
    (G : (Fin 10 → K) → K) (polys : Fin 10 → Polynomial K) (α : Fin 10 → K)
    (hG : ∀ b, G (ofBool b) = eqwB 10 zc b * lanesComp θ laneOf b + μ * H1 b + μ ^ 2 * inact b)
    (hdeg : IndDeg 27 10 G) (hacc : accept 27 10 G 0 polys α)
    (hα : ¬ BadAlpha 27 10 α)
    (hμ : ¬ BadMu (mle 10 (lanesComp θ laneOf) zc) (bsumB 10 H1) (bsumB 10 inact) μ)
    (hzc : ¬ BadZc (lanesComp θ laneOf) zc) (hθ : ¬ BadTheta laneOf θ) :
    ProductionHolds pub lam chi t ∧ CopyLinkBalance pub t := by
  obtain ⟨hlanes, h1, h2⟩ :=
    compose laneOf H1 inact θ μ zc G polys α hG hdeg hacc hα hμ hzc hθ
  have hprod : ProductionHolds pub lam chi t := hlane.mp hlanes
  exact ⟨hprod, hlogup lam chi hlc hprod.2.2.2.2.2.2.2 h1 h2⟩

/-- With the proposal's positivity lane (Finding 1: not a production lane),
the transfer amounts are positive integers. -/
theorem semantic_positivity (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)
    (pub : Public K) (t : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi t ∧ CopyLinkBalance pub t)
    (hpos : Holds positiveFamily pub t) :
    ∃ v0 v1 v2 : Nat, v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧ 1 ≤ v1 ∧ 1 ≤ v2 ∧
      v0 = v1 + v2 ∧ t 0 1014 = (v0 : K) ∧ t 1 1014 = (v1 : K) ∧ t 1 1015 = (v2 : K) :=
  positivity_of_balance P hP pub t h.1.1 hpos h.2

/-- G9's statement, as the assembly consumes it. -/
def ExtractionStep (pub : Public K) (lam chi : K) (t : Trace K) : Prop :=
  ProductionHolds pub lam chi t → CopyLinkBalance pub t → InputNoteExtracted pub t

theorem semantic_extraction (pub : Public K) (t : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi t ∧ CopyLinkBalance pub t)
    (hext : ExtractionStep pub lam chi t) : InputNoteExtracted pub t :=
  hext h.1 h.2

/-- G9 instantiates the extraction step. -/
theorem extraction_step (pub : Public K) (lam chi : K) (t : Trace K) :
    ExtractionStep pub lam chi t :=
  fun h hb => input_note_extracted pub t h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.1
    h.2.2.2.2.2.2.1 hb

#print axioms extraction_step
#print axioms semantic_sound
#print axioms semantic_positivity
#print axioms semantic_extraction
end R0P
