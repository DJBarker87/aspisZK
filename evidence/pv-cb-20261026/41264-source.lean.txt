import R1Z.PV_CB_CanonicalTower
set_option autoImplicit false
namespace R1Z.PV_CB_TowerLaneJoin
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_CanonicalTower.Q

theorem ext (left right : Q)
    (h0 : left.c0.a = right.c0.a) (h1 : left.c0.b = right.c0.b)
    (h2 : left.c1.a = right.c1.a) (h3 : left.c1.b = right.c1.b) : left = right := by
  rcases left with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases right with ⟨⟨a',b'⟩,⟨c',d'⟩⟩
  cases h0;cases h1;cases h2;cases h3;rfl

/-- Native successful outputs can be joined from all four word equalities;
    totality/error agreement is still required at a Result boundary. -/
theorem successful (left right : Result Q) (x y : Q)
    (hl : left = ok x) (hr : right = ok y)
    (h0 : x.c0.a = y.c0.a) (h1 : x.c0.b = y.c0.b)
    (h2 : x.c1.a = y.c1.a) (h3 : x.c1.b = y.c1.b) : left = right := by
  rw [hl,hr,ext x y h0 h1 h2 h3]
#print axioms ext
#print axioms successful
end R1Z.PV_CB_TowerLaneJoin
