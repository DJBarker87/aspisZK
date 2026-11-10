import NPH_R22JoinSM
import NHU_Mask

/-! NPH_ (R22, SM step 1): the semantic-boundary mask site.
`FIp_mask_site`: for every seed record, (FIp_SemanticArithmetic.install seed).mask on inputs
whose probe images are canonical (every c1, mask-only and point cell, and g) is ok with a
canonical output. This is NHU_Mask.result (closure theorem: state_only_selected_mask_value
is ok and canonical on canonical inputs, with all loop invariants and the 27-entry
coefficient array established by the imported coefficient/Horner/linear inductions)
transported by NHU_Mask.adopted. Since the whole state_only_selected_mask_value call is ok,
every SM kernel call it executes (the four loop bodies, the coefficient writes, the
prepared multiplier, mask_power_26 and the tail) returns ok. The four loop compositions
and the coefficient-array invariant of NPH_SITES.json are therefore subsumed at this site.
The producers of the canonical inputs at the FinishModel.finish call (claims decoder,
fromFn closures 9/5, claims[0][27], RoundModel alpha) are NOT composed here. Standard
axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM2
open Aeneas Aeneas.Std Result
open AspisR1.FIp_SemanticArithmetic

theorem FIp_mask_site (seed : AspisR1PublicPreparation.FinishModel.Boundaries)
    (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize)
    (hc1 : ∀ j : Fin 16, AspisR1.ExtractedMaskCallerModel.CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell (mapArray c1) j))
    (hm : ∀ j : Fin 10, AspisR1.ExtractedMaskCallerModel.CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell (mapArray m) j))
    (hp : ∀ i (hi : i < 10), AspisR1.ExtractedMaskCallerModel.CanonicalQM
      (AspisR1.ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (hg : AspisR1.ExtractedMaskCallerModel.CanonicalQM (toProbe g)) :
    ∃ out, (install seed).mask c1 m g point = ok out ∧
      AspisR1.ExtractedMaskCallerModel.CanonicalQM (toProbe out) := by
  obtain ⟨out, h, hc, _⟩ := AspisR1.NHU_Mask.result (mapArray c1) (mapArray m) (toProbe g) (mapArray point)
    hc1 hm hp hg
  refine ⟨fromProbe out, ?_, hc⟩
  rw [AspisR1.NHU_Mask.adopted, h]
  rfl

#print axioms FIp_mask_site
end AspisR1.NPH_R22JoinSM2
