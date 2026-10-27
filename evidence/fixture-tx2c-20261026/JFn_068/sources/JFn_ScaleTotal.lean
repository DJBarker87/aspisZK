import SAQ_RawScale
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_ScaleTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem base (x y : U32) : ∃ z, field.M31.mul x y=ok z := by
  obtain ⟨z,run,_,_⟩ := ExtractedCurrentReducer.current_mul_mod x y
  exact ⟨z,(m31_mul_same x y).trans run⟩

theorem cm (x : field.CM31) (s : U32) : ∃ z, field.CM31.mul_m31 x s=ok z := by
  obtain ⟨a,ha⟩:=base x.a s
  obtain ⟨b,hb⟩:=base x.b s
  exact ⟨⟨a,b⟩,by simp only [field.CM31.mul_m31,ha,hb,bind_tc_ok]⟩

theorem qm (x : field.QM31) (s : U32) : ∃ z, field.QM31.mul_m31 x s=ok z := by
  obtain ⟨a,ha⟩:=cm x.c0 s
  obtain ⟨b,hb⟩:=cm x.c1 s
  exact ⟨⟨a,b⟩,by simp only [field.QM31.mul_m31,ha,hb,bind_tc_ok]⟩

/-- Forward totality for the actual scalar-multiplication body. Each
component executes the source reducer; no result-success premise is used. -/
theorem wide (x : E) (s : U32) :
    ∃ z, field.wide_exact.WideExact.mul_m31 x s=ok z ∧ CanonicalWide z := by
  obtain ⟨r,hr,_⟩:=WP.spec_imp_exists (UScalar.rem_spec s (y:=field.P) (by decide))
  obtain ⟨a,ha⟩:=qm x.c0 r
  obtain ⟨b,hb⟩:=qm x.c1 r
  have run : field.wide_exact.WideExact.mul_m31 x s=ok (⟨a,b⟩ : E) := by
    simp only [field.wide_exact.WideExact.mul_m31,hr,ha,hb,bind_tc_ok]
  exact ⟨_,run,(SAQ_RawScale.wide_mul_m31_success x _ s run).1⟩

#print axioms base
#print axioms cm
#print axioms qm
#print axioms wide
end AspisR1.JFn_ScaleTotal
end
