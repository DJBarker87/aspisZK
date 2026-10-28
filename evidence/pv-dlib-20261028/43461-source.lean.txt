import R1Z.PV_DL_BatchPlan
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_UpdateViews
set_option autoImplicit false

def views : Nat → List U8 → List (List U8)
  | 0,_ => []
  | n+1,input => input.take 64::views n (input.drop 64)

theorem count (n : Nat) (input : List U8) : (views n input).length=n := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp only [views,List.length_cons,ih]

theorem joined (n : Nat) (input : List U8) :
    (views n input).flatMap id=input.take (64*n) := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    simp only [views,List.flatMap_cons,id_eq,ih]
    rw [← List.take_add]
    congr 1
    omega

theorem coordinate (n i : Nat) (input : List U8) (hi : i<n) :
    (views n input)[i]?=some ((input.drop (64*i)).take 64) := by
  induction n generalizing input i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [views,List.getElem?_cons_succ]
      rw [ih i (input.drop 64) (by omega)]
      simp only [List.drop_drop]
      congr 3
      omega

theorem byte (input : List U8) (i j : Nat) (hj : j<64) :
    ((input.drop (64*i)).take 64)[j]?=input[64*i+j]? := by
  simp only [List.getElem?_take,List.getElem?_drop,if_pos hj,Nat.add_comm]

theorem lengths (n : Nat) (input : List U8) (bound : 64*n ≤ input.length)
    (block : List U8) (h : block∈views n input) : block.length=64 := by
  induction n generalizing input with
  | zero => simp only [views,List.not_mem_nil] at h
  | succ n ih =>
    simp only [views,List.mem_cons] at h
    rcases h with rfl|h
    · simp only [List.length_take]
      omega
    · apply ih (input.drop 64) _ h
      simp only [List.length_drop]
      omega

theorem native_bulk (input : List U8) :
    (views (input.length/64) input).flatMap id=(PV_DL_BatchPlan.bulk input).1 := by
  rw [joined]
  simp only [PV_DL_BatchPlan.bulk,Nat.mul_comm]

theorem native_block_lengths (input : List U8) (block : List U8)
    (h : block∈views (input.length/64) input) : block.length=64 :=
  lengths _ input (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self input.length 64) block h

#print axioms views
#print axioms count
#print axioms joined
#print axioms coordinate
#print axioms byte
#print axioms lengths
#print axioms native_bulk
#print axioms native_block_lengths
end R1Z.PV_DL_UpdateViews
