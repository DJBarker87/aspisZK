import NDO_JGd_Horner00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_HornerValue
open JGd_ExactWords JGd_HornerData
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

theorem source : ExtractedMaskHornerPolynomial.coefficientPolynomial coeff
    (value JGd_Linear00.sum0) = value JGd_Horner00.r00 := by
  rw [← ExtractedMaskHornerPolynomial.generic_seed_coefficient_26_eq_polynomial,seed]
  change run 26 (value r26) = value JGd_Horner00.r00
  dsimp only [r26]
  rw [JGd_Horner25.step]
  dsimp only [JGd_Horner25.r25]
  rw [JGd_Horner24.step]
  dsimp only [JGd_Horner24.r24]
  rw [JGd_Horner23.step]
  dsimp only [JGd_Horner23.r23]
  rw [JGd_Horner22.step]
  dsimp only [JGd_Horner22.r22]
  rw [JGd_Horner21.step]
  dsimp only [JGd_Horner21.r21]
  rw [JGd_Horner20.step]
  dsimp only [JGd_Horner20.r20]
  rw [JGd_Horner19.step]
  dsimp only [JGd_Horner19.r19]
  rw [JGd_Horner18.step]
  dsimp only [JGd_Horner18.r18]
  rw [JGd_Horner17.step]
  dsimp only [JGd_Horner17.r17]
  rw [JGd_Horner16.step]
  dsimp only [JGd_Horner16.r16]
  rw [JGd_Horner15.step]
  dsimp only [JGd_Horner15.r15]
  rw [JGd_Horner14.step]
  dsimp only [JGd_Horner14.r14]
  rw [JGd_Horner13.step]
  dsimp only [JGd_Horner13.r13]
  rw [JGd_Horner12.step]
  dsimp only [JGd_Horner12.r12]
  rw [JGd_Horner11.step]
  dsimp only [JGd_Horner11.r11]
  rw [JGd_Horner10.step]
  dsimp only [JGd_Horner10.r10]
  rw [JGd_Horner09.step]
  dsimp only [JGd_Horner09.r09]
  rw [JGd_Horner08.step]
  dsimp only [JGd_Horner08.r08]
  rw [JGd_Horner07.step]
  dsimp only [JGd_Horner07.r07]
  rw [JGd_Horner06.step]
  dsimp only [JGd_Horner06.r06]
  rw [JGd_Horner05.step]
  dsimp only [JGd_Horner05.r05]
  rw [JGd_Horner04.step]
  dsimp only [JGd_Horner04.r04]
  rw [JGd_Horner03.step]
  dsimp only [JGd_Horner03.r03]
  rw [JGd_Horner02.step]
  dsimp only [JGd_Horner02.r02]
  rw [JGd_Horner01.step]
  dsimp only [JGd_Horner01.r01]
  rw [JGd_Horner00.step]
  rfl
#print axioms source
end AspisR1.JGd_HornerValue
end
