import FJn_MaskInputCanonical
import FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic
/-- Actual installed mask VALUE and canonicality, with canonical original
operands; no second chosen output and no assumed model result. -/
theorem value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ)
    (point : Array MQ 10#usize) (out : MQ)
    (hc : ∀ x∈c1.val,FIp_SemanticValues.Canon x)
    (hm : ∀ x∈m.val,FIp_SemanticValues.Canon x)
    (hp : ∀ x∈point.val,FIp_SemanticValues.Canon x)
    (hg : FIp_SemanticValues.Canon g)
    (run : FIp_SemanticArithmetic.mask c1 m g point=ok out) :
    FIp_SemanticValues.Canon out ∧ FIp_SemanticValues.decode out=FIp_MaskValue.value c1 m g point := by
  have cc : ∀ i : Fin 16,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) i) := by
    intro i
    exact FJn_MaskInputCanonical.cell c1 hc i.val (by rw [c1.property];exact i.isLt)
  have mc : ∀ i : Fin 10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.maskCell (mapArray m) i) := by
    intro i
    exact FJn_MaskInputCanonical.cell m hm i.val (by rw [m.property];exact i.isLt)
  have pc : ∀ i : Nat,∀ hi : i<10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi) := by
    intro i hi
    exact FJn_MaskInputCanonical.cell point hp i (by rw [point.property];exact hi)
  obtain ⟨native,called,can,val⟩:=FIp_MaskNativeValue.source c1 m g point cc mc pc hg
  have same : fromProbe native=out:=Result.ok.inj (called.symm.trans run)
  subst out
  refine ⟨?_,?_⟩
  · simpa only [FIp_SemanticValues.Canon,FIp_SemanticValues.to_from] using can
  · simpa only [FIp_SemanticValues.decode,FIp_SemanticValues.to_from,FIp_MaskValue.value] using val
#print axioms value
end AspisR1.FJn_MaskValue
end
