import FJn_MaskInputCanonical
import FJn_MaskDecode
import ExtractedMaskSemanticBridgeConcrete
import FIz_ConcretePack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskWide
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic
open FIz_ConcretePack (embed)
def cell {N : Usize} (a : Array MQ N) (i : Fin N.val) :=
  embed (FIp_SemanticValues.decode (a.val[i.val]'(by rw [a.property];exact i.isLt)))
attribute [local irreducible] embed R0P.Mask.maskValue
/-- The actual installed mask computes the original R0P mask model in Wide. -/
theorem value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ)
    (point : Array MQ 10#usize) (out : MQ)
    (hc : ∀ x∈c1.val,FIp_SemanticValues.Canon x)
    (hm : ∀ x∈m.val,FIp_SemanticValues.Canon x)
    (hp : ∀ x∈point.val,FIp_SemanticValues.Canon x)
    (hg : FIp_SemanticValues.Canon g)
    (run : FIp_SemanticArithmetic.mask c1 m g point=ok out) :
    FIp_SemanticValues.Canon out ∧ embed (FIp_SemanticValues.decode out)=
      R0P.Mask.maskValue ConcretePackBasis.basis (cell c1) (cell m)
        (embed (FIp_SemanticValues.decode g)) (cell point) := by
  have cc : ∀ i : Fin 16,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) i) := by
    intro i;exact FJn_MaskInputCanonical.cell c1 hc i.val (by rw [c1.property];exact i.isLt)
  have mc : ∀ i : Fin 10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.maskCell (mapArray m) i) := by
    intro i;exact FJn_MaskInputCanonical.cell m hm i.val (by rw [m.property];exact i.isLt)
  have pc : ∀ i : Nat,∀ hi : i<10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi) := by
    intro i hi;exact FJn_MaskInputCanonical.cell point hp i (by rw [point.property];exact hi)
  obtain ⟨native,called,can,val⟩:=ExtractedMaskSemanticBridgeConcrete.current_selected_mask_maps_to_maskValue
    (mapArray c1) (mapArray m) (toProbe g) (mapArray point) cc mc pc hg
  have actual : FIp_SemanticArithmetic.mask c1 m g point=ok (fromProbe native) := by
    unfold FIp_SemanticArithmetic.mask
    rw [called]
    rfl
  cases Result.ok.inj (actual.symm.trans run)
  refine ⟨?_,?_⟩
  · simpa only [FIp_SemanticValues.Canon,FIp_SemanticValues.to_from] using can
  · rw [FJn_MaskDecode.value]
    simpa only [
      _private.ExtractedMaskSemanticBridgeConcrete.0.AspisR1.ExtractedMaskSemanticBridgeConcrete.decode,
      _private.ExtractedMaskSemanticBridgeConcrete.0.AspisR1.ExtractedMaskSemanticBridgeConcrete.mappedC1Cell,
      _private.ExtractedMaskSemanticBridgeConcrete.0.AspisR1.ExtractedMaskSemanticBridgeConcrete.mappedMaskCell,
      _private.ExtractedMaskSemanticBridgeConcrete.0.AspisR1.ExtractedMaskSemanticBridgeConcrete.mappedPoint,
      cell,FIz_ConcretePack.embed,ExtractedMaskSemanticBridgeConcrete.qm31ToWide,
      ExtractedMaskSemanticBridgeConcrete.packBasis,FIp_SemanticValues.decode,
      ExtractedMaskCoefficientStep.c1Cell,ExtractedMaskCoefficientStep.maskCell,
      ExtractedMaskLinearsExact.decodedPoint,ExtractedMaskLinearLoop.pointAtNat,
      mapArray,List.getElem_map] using val
#print axioms value
end AspisR1.FJn_MaskWide
end
