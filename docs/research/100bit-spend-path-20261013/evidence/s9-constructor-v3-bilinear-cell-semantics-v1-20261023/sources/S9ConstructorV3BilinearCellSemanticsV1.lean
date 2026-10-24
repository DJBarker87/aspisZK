import S9ConstructorV3QMMulSemanticsV1
import S9ConstructorV3QMAddSubSemanticsV1
import S9ConstructorTensorFactorMapV1
import S9ConstructorV3Loop1CellCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3BilinearCellSemanticsV1
open AspisR1S9ConstructorV3QMMulSemanticsV1

/-- The six arithmetic calls made by the actual statement-factor cell produce
its four intended bilinear coefficients. The enclosing source-body theorem
must derive these calls from its single accepted execution. -/
theorem bilinear_cell_success_exact
    (a b u v q0 q1 q2 q3 : SourceQM) (ha : Can a) (hb : Can b)
    (hu : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE a = .ok u)
    (hv : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE b = .ok v)
    (h0 : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u v = .ok q0)
    (h1 : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a v = .ok q1)
    (h2 : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u b = .ok q2)
    (h3 : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a b = .ok q3) :
    Can q0 ∧ Can q1 ∧ Can q2 ∧ Can q3 ∧
    decode q0 = (1 - decode a) * (1 - decode b) ∧
    decode q1 = decode a * (1 - decode b) ∧
    decode q2 = (1 - decode a) * decode b ∧
    decode q3 = decode a * decode b := by
  have hone : Can AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE :=
    AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  obtain ⟨huc, hud⟩ :=
    AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE a u hone ha hu
  obtain ⟨hvc, hvd⟩ :=
    AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE b v hone hb hv
  obtain ⟨hc0, hd0⟩ := generated_mul_success_exact u v q0 huc hvc h0
  obtain ⟨hc1, hd1⟩ := generated_mul_success_exact a v q1 ha hvc h1
  obtain ⟨hc2, hd2⟩ := generated_mul_success_exact u b q2 huc hb h2
  obtain ⟨hc3, hd3⟩ := generated_mul_success_exact a b q3 ha hb h3
  change decode u = decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE - decode a at hud
  change decode v = decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE - decode b at hvd
  have ho := AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode
  rw [ho] at hud hvd
  exact ⟨hc0, hc1, hc2, hc3, by rw [hd0, hud, hvd],
    by rw [hd1, hvd], by rw [hd2, hud], hd3⟩

#print axioms bilinear_cell_success_exact
end AspisR1S9ConstructorV3BilinearCellSemanticsV1
