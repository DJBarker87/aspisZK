import NMX_R3_LaneModels
set_option autoImplicit false
namespace NMX_R3_BoolReject
open RSL

theorem join (a b : Bool) (next : Option LaneState) :
 (if a then none else if b then none else next) = if a || b then none else next := by
 cases a <;> rfl

theorem accept_guard (a : Bool) (next : Option LaneState) :
 (if a then next else none) = if !a then none else next := by
 cases a <;> rfl

theorem chain5 (a b c d e : Bool) (next : Option LaneState) :
 (if a then (if b then none else if c then none else if d then none else if e then none else next) else none) =
 (if !a || b || c || d || e then none else next) := by
 rw [accept_guard, ← join (!a || b || c || d) e, ← join (!a || b || c) d,
  ← join (!a || b) c, ← join (!a) b]
theorem chain7 (a b c d e f g : Bool) (next : Option LaneState) :
 (if a then (if b then none else if c then none else if d then none else if e then none
  else if f then (if g then next else none) else none) else none) =
 (if !a || b || c || d || e || !f || !g then none else next) := by
 cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem any_ne (bs : Bytes) : bs.any (· != 0) = !(bs.all (· == 0)) := by
 induction bs with
 | nil => rfl
 | cons b bs ih =>
  rw [List.any_cons, List.all_cons, ih]
  simp only [Bool.not_and, bne]
#print axioms chain7
#print axioms any_ne

theorem as_bool {A : Type} (p : Prop) [Decidable p] (yes no : A) :
 (if p then yes else no) = (if decide p then yes else no) := by
 by_cases h : p <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
#print axioms as_bool

#print axioms join
#print axioms accept_guard
#print axioms chain5
end NMX_R3_BoolReject
