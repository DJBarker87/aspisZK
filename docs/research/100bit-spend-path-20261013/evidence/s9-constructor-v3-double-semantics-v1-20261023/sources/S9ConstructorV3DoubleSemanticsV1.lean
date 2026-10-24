import S9ConstructorV3QMMulSemanticsV1
import S9ConstructorV3QMAddSubSemanticsV1
import S9ConstructorTensorFactorMapV1
import S9ConstructorV3Loop1CellCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3DoubleSemanticsV1
open AspisR1S9ConstructorV3QMMulSemanticsV1

/-- The actual constructor double call has the Chebyshev doubling expression;
all three arithmetic successes are derived from that same call. -/
theorem generated_double_success_exact (x z : SourceQM) (hx : Can x)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.double x = .ok z) :
    Can z ∧ decode z = decode x * decode x + decode x * decode x - 1 := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.double at hcall
  obtain ⟨q,hm,hcall⟩ :=
    AspisR1S9ConstructorV3Loop2InnerCanonicalV1.bind_success_inv _ _ _ hcall
  obtain ⟨q1,ha,hcall⟩ :=
    AspisR1S9ConstructorV3Loop2InnerCanonicalV1.bind_success_inv _ _ _ hcall
  have hs := hcall
  obtain ⟨hc,hd⟩ := generated_mul_success_exact x x q hx hx hm
  obtain ⟨hc1,hd1⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_add_success_exact
    q q q1 hc hc ha
  have hone : Can AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE :=
    AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  obtain ⟨hcz,hdz⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
    q1 AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE z hc1 hone hs
  change decode q1 = decode q + decode q at hd1
  change decode z = decode q1 - decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE at hdz
  exact ⟨hcz, by rw [hdz,hd1,hd,AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode]⟩

#print axioms generated_double_success_exact
end AspisR1S9ConstructorV3DoubleSemanticsV1
