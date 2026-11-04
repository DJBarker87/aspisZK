import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_FieldLaws
open Aeneas Aeneas.Std Result WP
/-- Natural-number spec paired with the native scalar field contract. -/
theorem neg_value (x : U32) (canonical : x.val < 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.neg x = ok z ∧
      z.val = (if x.val=0 then 0 else 2147483647-x.val) ∧ z.val<2147483647 := by
  by_cases zero : x=0#u32
  · subst x
    exact ⟨0#u32,rfl,rfl,by decide⟩
  · have nz : x.val ≠ 0 := by intro h;apply zero;apply UScalar.eq_of_val_eq;exact h
    have spec := @UScalar.sub_spec .U32 (2147483647#u32) x
      (by change x.val ≤ 2147483647;omega)
    obtain ⟨z,run,value,_⟩:=WP.spec_imp_exists spec
    refine ⟨z,?_,?_,?_⟩
    · simp only [AspisR1SelectedMaskProbe.field.M31.neg,if_neg zero,
        AspisR1SelectedMaskProbe.field.P,run,bind_tc_ok]
    · simpa only [if_neg nz] using value
    · rw [value];omega

theorem cm_reference (x : U32) :
    AspisS1M31Embedding.aspis_core.field.CM31.from_m31 x =
      ok (⟨x,0#u32⟩ : AspisS1M31Embedding.aspis_core.field.CM31) := by
  simp only [AspisS1M31Embedding.aspis_core.field.CM31.from_m31,
    AspisS1M31Embedding.aspis_core.field.M31.ZERO]

theorem qm_reference (x : AspisS1M31Embedding.aspis_core.field.CM31) :
    AspisS1M31Embedding.aspis_core.field.QM31.from_cm31 x =
      ok (⟨x,⟨0#u32,0#u32⟩⟩ : AspisS1M31Embedding.aspis_core.field.QM31) := by
  simp only [AspisS1M31Embedding.aspis_core.field.QM31.from_cm31,
    AspisS1M31Embedding.aspis_core.field.CM31.ZERO,
    AspisS1M31Embedding.aspis_core.field.M31.ZERO]
#print axioms neg_value
#print axioms cm_reference
#print axioms qm_reference
end NFQ_FieldLaws
