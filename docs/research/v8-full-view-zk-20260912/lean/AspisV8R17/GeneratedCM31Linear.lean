import AspisV8R17.GeneratedM31Add

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::sub"]
def aspis_core.field.CM31.sub
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.sub self.a rhs.a
  let m1 ← aspis_core.field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::add"]
def aspis_core.field.CM31.add
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.add self.a rhs.a
  let m1 ← aspis_core.field.M31.add self.b rhs.b
  ok { a := m, b := m1 }
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::double"]
def aspis_core.field.CM31.double
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  aspis_core.field.CM31.add self self
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedCM31Linear
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer

def Canonical (x : aspis_core.field.CM31) : Prop := x.a.val < P ∧ x.b.val < P

theorem generated_add_words (x y : aspis_core.field.CM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.CM31.add x y = .ok z ∧ Canonical z ∧
      z.a.val = (x.a.val+y.a.val)%P ∧ z.b.val = (x.b.val+y.b.val)%P := by
  obtain ⟨a, ea, va, ca⟩ := GeneratedM31Add.generated_add_mod x.a y.a hx.1 hy.1
  obtain ⟨b, eb, vb, cb⟩ := GeneratedM31Add.generated_add_mod x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩, by simp only [aspis_core.field.CM31.add, ea, eb, bind_tc_ok],
    ⟨ca,cb⟩, va, vb⟩

theorem generated_sub_words (x y : aspis_core.field.CM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.CM31.sub x y = .ok z ∧ Canonical z ∧
      z.a.val = (x.a.val+P-y.a.val)%P ∧ z.b.val = (x.b.val+P-y.b.val)%P := by
  obtain ⟨a, ea, va, ca⟩ := GeneratedM31Sub.generated_sub_mod x.a y.a hx.1 hy.1
  obtain ⟨b, eb, vb, cb⟩ := GeneratedM31Sub.generated_sub_mod x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩, by simp only [aspis_core.field.CM31.sub, ea, eb, bind_tc_ok],
    ⟨ca,cb⟩, va, vb⟩

theorem generated_double_words (x : aspis_core.field.CM31) (hx : Canonical x) :
    ∃ z, aspis_core.field.CM31.double x = .ok z ∧ Canonical z ∧
      z.a.val = (x.a.val+x.a.val)%P ∧ z.b.val = (x.b.val+x.b.val)%P :=
  generated_add_words x x hx hx

theorem subtraction_int (x y : Nat) (hx : x<P) (hy : y<P) :
    (((x+P-y)%P : Nat) : Int) = ((x : Int)-y)%(P : Int) := by
  unfold P at *
  omega

theorem generated_sub_residues (x y : aspis_core.field.CM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.CM31.sub x y = .ok z ∧ Canonical z ∧
      (z.a.val : Int) = ((x.a.val : Int)-y.a.val)%(P : Int) ∧
      (z.b.val : Int) = ((x.b.val : Int)-y.b.val)%(P : Int) := by
  obtain ⟨z, ez, cz, va, vb⟩ := generated_sub_words x y hx hy
  refine ⟨z, ez, cz, ?_, ?_⟩
  · rw [va]; exact subtraction_int _ _ hx.1 hy.1
  · rw [vb]; exact subtraction_int _ _ hx.2 hy.2

#print axioms generated_add_words
#print axioms generated_sub_words
#print axioms generated_double_words
#print axioms subtraction_int
#print axioms generated_sub_residues
end AspisV8R17.GeneratedCM31Linear
