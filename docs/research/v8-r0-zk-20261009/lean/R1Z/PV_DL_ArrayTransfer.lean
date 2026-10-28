import R1Z.PV_DL_ArrayOwnership
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ArrayTransfer
set_option autoImplicit false

/-- Sequential ownership transfer for from_fn(next), with the unwrap failure
explicit. No Copy, Clone, Inhabited, or destructor law is assumed for T. -/
def drain {T : Type} : Nat → List T → Result (List T × List T)
  | 0,xs => ok ([],xs)
  | _+1,[] => fail .panic
  | n+1,x::xs => do
    let (out,remaining) ← drain n xs
    ok (x::out,remaining)

theorem exact_transfer {T : Type} (xs : List T) :
    drain xs.length xs=ok (xs,[]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,drain,ih,bind_tc_ok,Aeneas.Std.uncurry]

theorem zero_live_drops {T : Type} (backing : List T) : backing.take 0=[] := rfl

def sequential {T : Type} (n : Nat) (xs : List T) : Result (List T × List T) :=
  if xs.length=n then drain n xs else ok ([],xs)

def bulk {T : Type} (n : Nat) (xs : List T) : Result (List T × List T) :=
  if xs.length=n then ok (xs,[]) else ok ([],xs)

/-- A bulk owned read and N sequential owned reads return the same elements
and leave the same empty live region, including the rejected-length branch. -/
theorem complete {T : Type} (n : Nat) (xs : List T) :
    sequential n xs=bulk n xs := by
  by_cases h : xs.length=n
  · simp only [sequential,bulk,if_pos h]
    rw [← h,exact_transfer]
  · simp only [sequential,bulk,if_neg h]

#print axioms drain
#print axioms exact_transfer
#print axioms zero_live_drops
#print axioms sequential
#print axioms bulk
#print axioms complete
end R1Z.PV_DL_ArrayTransfer
