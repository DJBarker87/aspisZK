import R1Z.PV_CBL_SplitModel
namespace R1Z.PV_AL_BlockPrefix
set_option autoImplicit false

def blocks {T : Type} (xs : List T) (size : Nat) : Nat → List (List T)
  | 0 => []
  | n+1 => blocks xs size n ++ [PV_CBL_SplitModel.block xs size n]

theorem length {T : Type} (xs : List T) (size count : Nat) :
    (blocks xs size count).length=count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [blocks,List.length_append,List.length_singleton,ih]

theorem representation {T : Type} (xs : List T) (size count : Nat) :
    blocks xs size count=(List.range count).map (PV_CBL_SplitModel.block xs size) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [blocks,List.range_succ,List.map_append,List.map_cons,List.map_nil,ih]

theorem concatenation {T : Type} (xs : List T) (size count : Nat)
    (h : count*size ≤ xs.length) :
    (blocks xs size count).flatten=xs.take (count*size) := by
  induction count with
  | zero => simp [blocks]
  | succ n ih =>
    have hb : n*size ≤ xs.length := le_trans
      (Nat.mul_le_mul_right size (Nat.le_succ n)) h
    simp only [blocks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,ih hb,
      PV_CBL_SplitModel.block]
    rw [←List.take_add]
    congr 1
    simp only [Nat.add_mul,Nat.one_mul]

#print axioms blocks
#print axioms length
#print axioms representation
#print axioms concatenation
end R1Z.PV_AL_BlockPrefix
