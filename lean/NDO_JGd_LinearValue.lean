import NDO_JGd_Linear00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_LinearValue
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
theorem family0 : ExtractedMaskLinearRecurrence.maskLinear 0
    (ExtractedMaskLinearsExact.decodedPoint (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.point)) = value JGd_Linear00.sum0 := by
  unfold ExtractedMaskLinearRecurrence.maskLinear
  simp only [JGd_LinearInputs.decoded,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero]
  change ((3:Q)*value (JGd_LinearInputs.point ⟨0,by omega⟩)+((25:Q)*value (JGd_LinearInputs.point ⟨1,by omega⟩)+((47:Q)*value (JGd_LinearInputs.point ⟨2,by omega⟩)+((69:Q)*value (JGd_LinearInputs.point ⟨3,by omega⟩)+((91:Q)*value (JGd_LinearInputs.point ⟨4,by omega⟩)+((113:Q)*value (JGd_LinearInputs.point ⟨5,by omega⟩)+((135:Q)*value (JGd_LinearInputs.point ⟨6,by omega⟩)+((157:Q)*value (JGd_LinearInputs.point ⟨7,by omega⟩)+((179:Q)*value (JGd_LinearInputs.point ⟨8,by omega⟩)+((201:Q)*value (JGd_LinearInputs.point ⟨9,by omega⟩)+value ((0,0),(0,0))))))))))))=value JGd_Linear00.sum0
  rw [JGd_Linear00.weighted0,JGd_Linear01.weighted0,JGd_Linear02.weighted0,JGd_Linear03.weighted0,JGd_Linear04.weighted0,JGd_Linear05.weighted0,JGd_Linear06.weighted0,JGd_Linear07.weighted0,JGd_Linear08.weighted0,JGd_Linear09.weighted0]
  change value JGd_Linear00.term0 + _ = _
  rw [JGd_Linear09.added0]
  dsimp only [JGd_Linear09.sum0]
  rw [JGd_Linear08.added0]
  dsimp only [JGd_Linear08.sum0]
  rw [JGd_Linear07.added0]
  dsimp only [JGd_Linear07.sum0]
  rw [JGd_Linear06.added0]
  dsimp only [JGd_Linear06.sum0]
  rw [JGd_Linear05.added0]
  dsimp only [JGd_Linear05.sum0]
  rw [JGd_Linear04.added0]
  dsimp only [JGd_Linear04.sum0]
  rw [JGd_Linear03.added0]
  dsimp only [JGd_Linear03.sum0]
  rw [JGd_Linear02.added0]
  dsimp only [JGd_Linear02.sum0]
  rw [JGd_Linear01.added0]
  dsimp only [JGd_Linear01.sum0]
  rw [JGd_Linear00.added0]
#print axioms family0
theorem family16 : ExtractedMaskLinearRecurrence.maskLinear 16
    (ExtractedMaskLinearsExact.decodedPoint (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.point)) = value JGd_Linear00.sum16 := by
  unfold ExtractedMaskLinearRecurrence.maskLinear
  simp only [JGd_LinearInputs.decoded,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero]
  change ((275:Q)*value (JGd_LinearInputs.point ⟨0,by omega⟩)+((425:Q)*value (JGd_LinearInputs.point ⟨1,by omega⟩)+((575:Q)*value (JGd_LinearInputs.point ⟨2,by omega⟩)+((725:Q)*value (JGd_LinearInputs.point ⟨3,by omega⟩)+((875:Q)*value (JGd_LinearInputs.point ⟨4,by omega⟩)+((1025:Q)*value (JGd_LinearInputs.point ⟨5,by omega⟩)+((1175:Q)*value (JGd_LinearInputs.point ⟨6,by omega⟩)+((1325:Q)*value (JGd_LinearInputs.point ⟨7,by omega⟩)+((1475:Q)*value (JGd_LinearInputs.point ⟨8,by omega⟩)+((1625:Q)*value (JGd_LinearInputs.point ⟨9,by omega⟩)+value ((0,0),(0,0))))))))))))=value JGd_Linear00.sum16
  rw [JGd_Linear00.weighted16,JGd_Linear01.weighted16,JGd_Linear02.weighted16,JGd_Linear03.weighted16,JGd_Linear04.weighted16,JGd_Linear05.weighted16,JGd_Linear06.weighted16,JGd_Linear07.weighted16,JGd_Linear08.weighted16,JGd_Linear09.weighted16]
  change value JGd_Linear00.term16 + _ = _
  rw [JGd_Linear09.added16]
  dsimp only [JGd_Linear09.sum16]
  rw [JGd_Linear08.added16]
  dsimp only [JGd_Linear08.sum16]
  rw [JGd_Linear07.added16]
  dsimp only [JGd_Linear07.sum16]
  rw [JGd_Linear06.added16]
  dsimp only [JGd_Linear06.sum16]
  rw [JGd_Linear05.added16]
  dsimp only [JGd_Linear05.sum16]
  rw [JGd_Linear04.added16]
  dsimp only [JGd_Linear04.sum16]
  rw [JGd_Linear03.added16]
  dsimp only [JGd_Linear03.sum16]
  rw [JGd_Linear02.added16]
  dsimp only [JGd_Linear02.sum16]
  rw [JGd_Linear01.added16]
  dsimp only [JGd_Linear01.sum16]
  rw [JGd_Linear00.added16]
#print axioms family16
end AspisR1.JGd_LinearValue
end
