import R0P.SemDegFamilies

/-! G14′: the unconditional degree bridge for the literal virtual terminal. -/
set_option autoImplicit false
noncomputable section
namespace R0P.SemDegree
open SemSource
variable {K : Type} [Field K]
attribute [local irreducible] VDeg honestClaims selAt laneAt activeAt eqValue

/-- Equality weighting adds one to the audited degree-26 lane bound. -/
theorem vdeg_terminalValue (pub : Public K) (t : Trace K) (lam chi θ μ : K)
    (zc : Fin 10 → K) {F : Subfield K} (B : PackBasis F) :
    VDeg 10 (fun _ => 27) (fun v => terminalValue pub lam chi θ μ zc B (honestClaims t v) v) := by
  have he := vdeg_eqValue zc
  have hh := vdeg_honestClaims_zero t 26
  have ha := vdeg_activeAt (K := K)
  have hs : VDeg 10 (fun _ => 26) (fun v => ∑ i : Fin 29,
      θ^i.val * laneAt pub lam chi B (openingsOf (honestClaims t v))
        (honestClaims t v 0 26) (selAt v) i) :=
    vdeg_sum _ _ (fun i _ => vdeg_smul (θ^i.val) (vdeg_laneAt pub t lam chi B i))
  change VDeg 10 (fun _ => 27) (fun v =>
    eqValue zc v * (∑ i : Fin 29, θ^i.val * laneAt pub lam chi B
      (openingsOf (honestClaims t v)) (honestClaims t v 0 26) (selAt v) i) +
    μ * honestClaims t v 0 26 + μ * μ * ((1-activeAt v) * honestClaims t v 0 26))
  degree_bound

#print axioms vdeg_terminalValue

theorem vdeg_virtualPoly (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (t : Trace K) (pre : Fin 14 → K) :
    VDeg 10 (fun _ => 27) (virtualPoly pub B t pre) :=
  vdeg_terminalValue pub t (pre 0) (pre 1) (pre 2) (pre 13) (preZc pre) B

#print axioms vdeg_virtualPoly
end R0P.SemDegree

namespace R0P.SemSource
variable {K : Type} [Field K]

/-- The original G14 degree obligation, with every input bound discharged. -/
theorem virtualDeg (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K) :
    VirtualDeg pub B t := by
  intro pre
  exact SemBadSets.mlDeg_indDeg
    (SemDegree.vdeg_mlDeg (SemDegree.vdeg_virtualPoly pub B t pre) (fun _ => le_rfl))

#print axioms virtualDeg
end R0P.SemSource
end
