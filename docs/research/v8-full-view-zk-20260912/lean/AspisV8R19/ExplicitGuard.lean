import AspisR69Explicit.Funs

/-! Exact fixed-arity guard and fallback behavior. Arithmetic success on all
canonical pairs and complete circle-map correctness remain separate goals. -/
set_option autoImplicit false
namespace AspisV8R19.ExplicitGuard
open Aeneas Aeneas.Std Result AspisR69Explicit

def badPair (left right : field.QM31) : Prop :=
  left.c0.a ≥ field.P ∨ left.c0.b ≥ field.P ∨
  left.c1.a ≥ field.P ∨ left.c1.b ≥ field.P ∨
  right.c0.a ≥ field.P ∨ right.c0.b ≥ field.P ∨
  right.c1.a ≥ field.P ∨ right.c1.b ≥ field.P

theorem guard_rejects (left right : field.QM31) (h : badPair left right) :
    field.r24_canonical_mul left right = .ok none := by
  rcases h with h|h|h|h|h|h|h|h <;>
    simp only [field.r24_canonical_mul,h,if_true,ite_self]

theorem fallback_retained (left right : field.QM31) (h : badPair left right) :
    field.QM31.mul left right = (do
      let m0 ← field.CM31.mul left.c0 right.c0
      let m1 ← field.CM31.mul left.c1 right.c1
      let c ← field.CM31.add left.c0 left.c1
      let c1 ← field.CM31.add right.c0 right.c1
      let m2 ← field.CM31.mul c c1
      let c2 ← field.mul_by_r m1
      let c3 ← field.CM31.add m0 c2
      let c4 ← field.CM31.sub m2 m0
      let c5 ← field.CM31.sub c4 m1
      .ok { c0 := c3, c1 := c5 }) := by
  simp only [field.QM31.mul,guard_rejects left right h,bind_tc_ok]

theorem option_some {T E : Type} (x : T) (e : E) :
    AspisR69Explicit.core.option.Option.ok_or (some x) e = .ok (.Ok x) := rfl

theorem option_none {T E : Type} (e : E) :
    AspisR69Explicit.core.option.Option.ok_or (none : Option T) e = .ok (.Err e) := rfl

#print axioms guard_rejects
#print axioms fallback_retained
#print axioms option_some
#print axioms option_none
#print axioms field.r24_canonical_mul
#print axioms circle.secure_circle_point_from_parameter
#print axioms circle.secure_ood_circle_point_from_parameter
end AspisV8R19.ExplicitGuard
