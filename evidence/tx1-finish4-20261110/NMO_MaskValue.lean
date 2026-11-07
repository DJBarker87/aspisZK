import NMO_MaskAtState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_MaskValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open ExtractedMaskCallerModel
/-- Field-preserving conversion, proved symbolically on four limbs. -/
theorem to_probe (q : Q) (h : NKQ_MaskCuts.Canon q) :
 CanonicalQM (FIp_SemanticArithmetic.toProbe q) := by
 simpa only [NKQ_MaskCuts.Canon,FIp_SemanticArithmetic.toProbe,
  CanonicalQM,ExtractedMaskCoefficientStep.CanonicalQM,
  ExtractedMaskTowerAdd.CanonicalQM,ExtractedMaskTowerAdd.CanonicalCM,
  ExtractedMaskTowerAdd.P,ExtractedMaskM31AddSub.P,and_assoc] using h
theorem from_probe (q : AspisR1SelectedMaskProbe.field.QM31) (h : CanonicalQM q) :
 NKQ_MaskCuts.Canon (FIp_SemanticArithmetic.fromProbe q) := by
 simpa only [NKQ_MaskCuts.Canon,FIp_SemanticArithmetic.fromProbe,
  CanonicalQM,ExtractedMaskCoefficientStep.CanonicalQM,
  ExtractedMaskTowerAdd.CanonicalQM,ExtractedMaskTowerAdd.CanonicalCM,
  ExtractedMaskTowerAdd.P,ExtractedMaskM31AddSub.P,and_assoc] using h
/-- The adopted mask's canonical result is obtained on exactly the caller's
array/scalar domain, without evaluating multiplication in Kani. -/
theorem source (reservation : NP6_StdModel.Reservation) (low : Low) (high : High) (blind : Q) (alpha : Alpha)
 (hl : ∀ q∈low.val,NKQ_MaskCuts.Canon q) (hh : ∀ q∈high.val,NKQ_MaskCuts.Canon q)
 (hb : NKQ_MaskCuts.Canon blind) (ha : NKQ_MaskCuts.CanonAlpha alpha) :
 ∃ value,(IDa_Deployed.boundaries reservation).mask low high blind alpha=ok value ∧ NKQ_MaskCuts.Canon value := by
 have lc : ∀ j : Fin 16,CanonicalQM (ExtractedMaskCoefficientStep.c1Cell (FIp_SemanticArithmetic.mapArray low) j) := by
  intro j
  let q:=low.val[j.val]'(by have len:=low.property;change low.val.length=16 at len;omega)
  have member : q∈low.val:=List.getElem_mem _
  simpa only [q,ExtractedMaskCoefficientStep.c1Cell,FIp_SemanticArithmetic.mapArray,List.getElem_map] using to_probe q (hl q member)
 have hc : ∀ j : Fin 10,CanonicalQM (ExtractedMaskCoefficientStep.maskCell (FIp_SemanticArithmetic.mapArray high) j) := by
  intro j
  let q:=high.val[j.val]'(by have len:=high.property;change high.val.length=10 at len;omega)
  have member : q∈high.val:=List.getElem_mem _
  simpa only [q,ExtractedMaskCoefficientStep.maskCell,FIp_SemanticArithmetic.mapArray,List.getElem_map] using to_probe q (hh q member)
 have ac : ∀ i : Nat,∀ hi : i<10,CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (FIp_SemanticArithmetic.mapArray alpha) i hi) := by
  intro i hi
  let q:=alpha.val[i]'(by have len:=alpha.property;change alpha.val.length=10 at len;omega)
  have member : q∈alpha.val:=List.getElem_mem _
  simpa only [q,ExtractedMaskLinearLoop.pointAtNat,FIp_SemanticArithmetic.mapArray,List.getElem_map] using to_probe q (ha q member)
 obtain ⟨value,returned,canonical,_⟩:=selected_mask_value_populated_model
  (FIp_SemanticArithmetic.mapArray low) (FIp_SemanticArithmetic.mapArray high)
  (FIp_SemanticArithmetic.toProbe blind) (FIp_SemanticArithmetic.mapArray alpha) lc hc ac (to_probe blind hb)
 refine ⟨FIp_SemanticArithmetic.fromProbe value,?_,from_probe value canonical⟩
 change FIp_SemanticArithmetic.mask low high blind alpha=ok (FIp_SemanticArithmetic.fromProbe value)
 unfold FIp_SemanticArithmetic.mask
 rw [returned]
 rfl
#print axioms to_probe
#print axioms from_probe
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMO_MaskValue
end
