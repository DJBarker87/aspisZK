import NFQ_FieldLaws
set_option autoImplicit false
namespace NFQ_FieldPorts
open Aeneas Aeneas.Std Result

theorem fiq_cm (x : U32) : FIq_Native.field.CM31.from_m31 x=
    ok (⟨x,0#u32⟩ : FIq_Native.field.CM31) := by
  simp only [FIq_Native.field.CM31.from_m31,FIq_Native.field.M31.ZERO]

theorem fiq_qm (x : FIq_Native.field.CM31) : FIq_Native.field.QM31.from_cm31 x=
    ok (⟨x,⟨0#u32,0#u32⟩⟩ : FIq_Native.field.QM31) := by
  simp only [FIq_Native.field.QM31.from_cm31,FIq_Native.field.CM31.ZERO]

theorem sampler_neg (x : U32) : AspisR72Sampler.field.M31.neg x=
    AspisR1SelectedMaskProbe.field.M31.neg x := by
  simp only [AspisR72Sampler.field.M31.neg,AspisR1SelectedMaskProbe.field.M31.neg,
    AspisR72Sampler.field.P,AspisR1SelectedMaskProbe.field.P]
#print axioms fiq_cm
#print axioms fiq_qm
#print axioms sampler_neg
end NFQ_FieldPorts
