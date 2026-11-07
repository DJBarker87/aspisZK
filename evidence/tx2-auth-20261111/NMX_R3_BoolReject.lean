import NMX_R3_LaneModels
set_option autoImplicit false
namespace NMX_R3_BoolReject
open RSL

theorem join (a b : Bool) (next : Option LaneState) :
 (if a then none else if b then none else next) = if a || b then none else next := by
 cases a <;> rfl

theorem unless (a : Bool) (next : Option LaneState) :
 (if a then next else none) = if !a then none else next := by
 cases a <;> rfl

theorem chain5 (a b c d e : Bool) (next : Option LaneState) :
 (if a then (if b then none else if c then none else if d then none else if e then none else next) else none) =
 (if !a || b || c || d || e then none else next) := by
 rw [unless, ← join (!a || b || c || d) e, ← join (!a || b || c) d,
  ← join (!a || b) c, ← join (!a) b]
#print axioms join
#print axioms unless
#print axioms chain5
end NMX_R3_BoolReject
