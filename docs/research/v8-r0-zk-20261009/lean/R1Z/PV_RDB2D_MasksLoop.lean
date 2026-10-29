import R1Z.PV_RDB2D_CollectorRequests
namespace R1Z.PV_RDB2D_MasksLoop
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Masks := List (BitVec 16)

def borrow (m : Masks) (index : Nat) : BitVec 16 × (BitVec 16 → Masks) :=
  (m[index]?.getD 0,fun value => m.set index value)

def borrowedStep (m : Masks) (row : Nat) : Masks :=
  let (value,restore) := borrow m (row/16)
  restore (value ||| ((1 : BitVec 16) <<< (row%16)))

def directStep (m : Masks) (row : Nat) : Masks :=
  m.set (row/16) (m[row/16]?.getD 0 ||| ((1 : BitVec 16) <<< (row%16)))

def run (rows : List Nat) (masks : Masks) : Masks := rows.foldl borrowedStep masks

theorem complete_restoration (m : Masks) (row : Nat) :
    borrowedStep m row=directStep m row := rfl

theorem length_preserved (m : Masks) (row : Nat) :
    (borrowedStep m row).length=m.length := List.length_set

theorem run_length (rows : List Nat) (m : Masks) : (run rows m).length=m.length := by
  induction rows generalizing m with
  | nil => rfl
  | cons r rs ih =>
    change (run rs (borrowedStep m r)).length=m.length
    rw [ih,length_preserved]

theorem block_bound (row : Nat) (h : row<1024) : row/16<64 := by omega

theorem shift_bound (row : Nat) : row%16<16 := Nat.mod_lt _ (by omega)

theorem append (left right : List Nat) (m : Masks) :
    run (left++right) m=run right (run left m) := List.foldl_append

theorem next_reads_current (m : Masks) (row : Nat) :
    (borrow m (row/16)).1=m[row/16]?.getD 0 := rfl

theorem restores_entire_list (m : Masks) (index : Nat) (value : BitVec 16) :
    (borrow m index).2 value=m.set index value := rfl

#print axioms complete_restoration
#print axioms length_preserved
#print axioms run_length
#print axioms block_bound
#print axioms shift_bound
#print axioms append
#print axioms next_reads_current
#print axioms restores_entire_list
end R1Z.PV_RDB2D_MasksLoop
