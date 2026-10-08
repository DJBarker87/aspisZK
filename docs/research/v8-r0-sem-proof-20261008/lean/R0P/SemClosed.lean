import R0P.SemAssembly
import R0P.LogUpAssembly
import R0P.LogUpChain
import R0P.LaneMap

/-! Lead: the closed SEM theorem for one candidate trace.

`semantic_sound_closed` instantiates `semantic_sound` with G11′'s lane map
(`lanes_zero_iff_holds`) and G12's LogUp chain (`logup_step_of` with
`logupL1`–`logupL5`). Hypotheses: base typing of the trace and of the
public input, a packing basis, characteristic P = 2^31 − 1, the terminal's
Boolean row value, the sumcheck's degree bound and acceptance of claim 0,
and the challenges outside the ledger's bad sets (α, μ, zc, θ, and
`BadLogUp` for λ, χ). Conclusion: every production family holds on the
trace and the copy links balance; hence `InputNoteExtracted`, and with
the proposal's positivity lane (Finding 1) the integer positivity. -/
set_option autoImplicit false
namespace R0P
open Sumcheck

variable {K : Type} [Field K]

theorem semantic_sound_closed (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)
    (F : Subfield K) (B : PackBasis F) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (lam chi θ μ : K) (zc : Fin 10 → K)
    (hlc : ¬ BadLogUp pub t lam chi)
    (G : (Fin 10 → K) → K) (polys : Fin 10 → Polynomial K) (α : Fin 10 → K)
    (hG : ∀ b, G (ofBool b) = eqwB 10 zc b * lanesComp θ (laneOf t pub lam chi B) b +
      μ * t 26 (rowOf b) +
      μ ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)))
    (hdeg : IndDeg 27 10 G) (hacc : accept 27 10 G 0 polys α)
    (hα : ¬ BadAlpha 27 10 α)
    (hμ : ¬ BadMu (mle 10 (lanesComp θ (laneOf t pub lam chi B)) zc)
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) μ)
    (hzc : ¬ BadZc (lanesComp θ (laneOf t pub lam chi B)) zc)
    (hθ : ¬ BadTheta (laneOf t pub lam chi B) θ) :
    ProductionHolds pub lam chi t ∧ CopyLinkBalance pub t := by
  have hlane : LaneInterface pub lam chi t (laneOf t pub lam chi B) :=
    lanes_zero_iff_holds F B pub lam chi t hA hpub
  have hlogup : LogUpStep pub t (BadLogUp pub t) (fun b => t 26 (rowOf b))
      (fun b => (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) :=
    logup_step_of pub t (fun lam chi => logupL1 pub t lam chi)
      (fun lam chi => logupL2 pub t lam chi) (fun lam chi => logupL3 pub t lam chi)
      (fun lam => logupL4 P hP pub t lam) (logupL5 P hP pub t) _ _
      (lane_h1_sum t) (lane_inactive_sum t)
  exact semantic_sound pub t lam chi θ μ zc (laneOf t pub lam chi B) hlane (BadLogUp pub t)
    _ _ hlogup hlc G polys α hG hdeg hacc hα hμ hzc hθ

/-- The extraction consequence. -/
theorem semantic_extraction_closed (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)
    (F : Subfield K) (B : PackBasis F) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (lam chi θ μ : K) (zc : Fin 10 → K) (hlc : ¬ BadLogUp pub t lam chi)
    (G : (Fin 10 → K) → K) (polys : Fin 10 → Polynomial K) (α : Fin 10 → K)
    (hG : ∀ b, G (ofBool b) = eqwB 10 zc b * lanesComp θ (laneOf t pub lam chi B) b +
      μ * t 26 (rowOf b) +
      μ ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)))
    (hdeg : IndDeg 27 10 G) (hacc : accept 27 10 G 0 polys α)
    (hα : ¬ BadAlpha 27 10 α)
    (hμ : ¬ BadMu (mle 10 (lanesComp θ (laneOf t pub lam chi B)) zc)
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) μ)
    (hzc : ¬ BadZc (lanesComp θ (laneOf t pub lam chi B)) zc)
    (hθ : ¬ BadTheta (laneOf t pub lam chi B) θ) :
    InputNoteExtracted pub t :=
  semantic_extraction pub t lam chi
    (semantic_sound_closed P hP F B pub t hA hpub lam chi θ μ zc hlc G polys α hG hdeg hacc
      hα hμ hzc hθ) (extraction_step pub lam chi t)

#print axioms semantic_sound_closed
#print axioms semantic_extraction_closed
end R0P
