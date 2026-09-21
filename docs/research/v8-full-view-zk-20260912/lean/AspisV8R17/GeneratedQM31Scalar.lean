import AspisV8R17.GeneratedCM31Linear
import AspisV8R17.GeneratedM31Mul

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED Types.lean
@[rust_type "aspis_core::field::QM31"]
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31
-- END GENERATED

-- GENERATED FunsChunk06.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul_m31"]
def aspis_core.field.CM31.mul_m31
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.mul self.a rhs
  let m1 ← aspis_core.field.M31.mul self.b rhs
  ok { a := m, b := m1 }
-- END GENERATED

-- GENERATED FunsChunk06.lean
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::mul_m31"]
def aspis_core.field.QM31.mul_m31
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.mul_m31 self.c0 rhs
  let c1 ← aspis_core.field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedQM31Scalar
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer

def Canonical (x : aspis_core.field.QM31) : Prop :=
  GeneratedCM31Linear.Canonical x.c0 ∧ GeneratedCM31Linear.Canonical x.c1

theorem cm31_scalar_words (x : aspis_core.field.CM31) (s : aspis_core.field.M31) :
    ∃ z, aspis_core.field.CM31.mul_m31 x s = .ok z ∧
      GeneratedCM31Linear.Canonical z ∧
      z.a.val = (x.a.val*s.val)%P ∧ z.b.val = (x.b.val*s.val)%P := by
  obtain ⟨a, ea, va, ca⟩ := GeneratedM31Mul.generated_mul_mod x.a s
  obtain ⟨b, eb, vb, cb⟩ := GeneratedM31Mul.generated_mul_mod x.b s
  exact ⟨⟨a,b⟩, by simp only [aspis_core.field.CM31.mul_m31, ea, eb, bind_tc_ok],
    ⟨ca,cb⟩, va, vb⟩

theorem qm31_scalar_words (x : aspis_core.field.QM31) (s : aspis_core.field.M31) :
    ∃ z, aspis_core.field.QM31.mul_m31 x s = .ok z ∧ Canonical z ∧
      z.c0.a.val = (x.c0.a.val*s.val)%P ∧ z.c0.b.val = (x.c0.b.val*s.val)%P ∧
      z.c1.a.val = (x.c1.a.val*s.val)%P ∧ z.c1.b.val = (x.c1.b.val*s.val)%P := by
  obtain ⟨a, ea, ca, va, wa⟩ := cm31_scalar_words x.c0 s
  obtain ⟨b, eb, cb, vb, wb⟩ := cm31_scalar_words x.c1 s
  exact ⟨⟨a,b⟩, by simp only [aspis_core.field.QM31.mul_m31, ea, eb, bind_tc_ok],
    ⟨ca,cb⟩, va, wa, vb, wb⟩

theorem half_scalar_double (x : Nat) (hx : x<P) :
    (2*((x*1073741824)%P))%P=x := by
  calc
    (2*((x*1073741824)%P))%P = (2*(x*1073741824))%P := by
      simp only [Nat.mul_mod, Nat.mod_mod]
    _ = (x*(2*1073741824))%P := by rw [Nat.mul_left_comm]
    _ = x := by
      rw [Nat.mul_mod]
      have hc : (2*1073741824)%P=1 := by decide
      rw [hc, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]

/-- The literal-value premise is explicit until the actual caller constant is bound. -/
theorem qm31_half_scalar (x : aspis_core.field.QM31) (hx : Canonical x)
    (s : aspis_core.field.M31) (hs : s.val=1073741824) :
    ∃ z, aspis_core.field.QM31.mul_m31 x s = .ok z ∧ Canonical z ∧
      (2*z.c0.a.val)%P=x.c0.a.val ∧ (2*z.c0.b.val)%P=x.c0.b.val ∧
      (2*z.c1.a.val)%P=x.c1.a.val ∧ (2*z.c1.b.val)%P=x.c1.b.val := by
  obtain ⟨z, ez, cz, v0, v1, v2, v3⟩ := qm31_scalar_words x s
  refine ⟨z, ez, cz, ?_, ?_, ?_, ?_⟩
  · rw [v0, hs]; exact half_scalar_double _ hx.1.1
  · rw [v1, hs]; exact half_scalar_double _ hx.1.2
  · rw [v2, hs]; exact half_scalar_double _ hx.2.1
  · rw [v3, hs]; exact half_scalar_double _ hx.2.2

#print axioms cm31_scalar_words
#print axioms qm31_scalar_words
#print axioms half_scalar_double
#print axioms qm31_half_scalar
end AspisV8R17.GeneratedQM31Scalar
