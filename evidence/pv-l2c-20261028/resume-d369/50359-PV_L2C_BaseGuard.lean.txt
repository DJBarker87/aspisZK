import PV_L2C_DecodeRange
set_option autoImplicit false
namespace PV_L2C_BaseGuard
open Aeneas Aeneas.Std Result
inductive Failure where
  | publicError

/-- Ascending native row scan; every first error is retained. `fuel` is the
remaining known row bound, not an added random or semantic assumption. -/
def loop : Nat → Nat → List U32 → Except Failure Unit
  | 0,_,_ => .ok ()
  | n+1,start,values =>
    if 2147483647 ≤ values[start]!.val then .error .publicError else loop n (start+1) values

def check (values : List U32) : Except Failure Unit :=
  if values.length ≠ 1024 then .error .publicError else loop 1024 0 values

theorem loop_ok (n start : Nat) (values : List U32)
    (hc : ∀ j, start ≤ j → j < start+n → values[j]!.val < 2147483647) :
    loop n start values = .ok () := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [loop,if_neg (by have := hc start (by omega) (by omega);omega)]
    exact ih (start+1) (by intro j hj hj';exact hc j (by omega) (by omega))
#print axioms loop_ok

theorem expected (values : List U32) (hl : values.length = 1024)
    (hc : ∀ j, j < 1024 → values[j]!.val < 2147483647) : check values = .ok () := by
  rw [check,if_neg (by omega)]
  exact loop_ok 1024 0 values (by intro j hj hj';exact hc j (by omega))
#print axioms expected

theorem rejects (values : List U32) (hl : values.length ≠ 1024) :
    check values = .error .publicError := by rw [check,if_pos hl]
#print axioms rejects
end PV_L2C_BaseGuard
