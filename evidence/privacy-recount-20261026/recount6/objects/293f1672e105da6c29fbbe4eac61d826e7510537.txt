import R1Z.ProverRwP6BodyGammaPort
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7CompressPrimitives
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
namespace Native
open AspisR1ProducerRelease47
theorem cm_scale (a : field.CM31) (b : field.M31) :
    ∃ c, field.CM31.mul_m31 a b = ok c := by
  obtain ⟨x,hx⟩ := ProverRwP6BaseTotal.mul a.a b
  obtain ⟨y,hy⟩ := ProverRwP6BaseTotal.mul a.b b
  exact ⟨⟨x,y⟩,by simp only [field.CM31.mul_m31,hx,hy,bind_tc_ok]⟩
theorem q_scale (a : field.QM31) (b : field.M31) :
    ∃ c, field.QM31.mul_m31 a b = ok c := by
  obtain ⟨x,hx⟩ := cm_scale a.c0 b
  obtain ⟨y,hy⟩ := cm_scale a.c1 b
  exact ⟨⟨x,y⟩,by simp only [field.QM31.mul_m31,hx,hy,bind_tc_ok]⟩
end Native
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected

theorem scale (ops : ExternalFuns) (a : Q) (b : U32) :
    ∃ c, (selected ops).op70 a b = ok c := by
  obtain ⟨c,hc⟩ := Native.q_scale (toQ a) b
  change ∃ c, mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ a) b) = ok c
  exact ⟨fromQ c,by rw [hc]; rfl⟩
theorem add (ops : ExternalFuns) (a b : Q) :
    ∃ c, (selected ops).op67 a b = ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.add (toQ a) (toQ b)
  change ∃ c, mapResult fromQ (AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)) = ok c
  exact ⟨fromQ c,by rw [hc]; rfl⟩
theorem mul (ops : ExternalFuns) (a b : Q) :
    ∃ c, (selected ops).op69 a b = ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.mul (toQ a) (toQ b)
  change ∃ c, mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)) = ok c
  exact ⟨fromQ c,by rw [hc]; rfl⟩
#print axioms Native.cm_scale
#print axioms Native.q_scale
#print axioms scale
#print axioms add
#print axioms mul
end R1Z.ProverRwP7CompressPrimitives
