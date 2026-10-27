import R1Z.PV_CB3_StagedMachinePass
import R1Z.PV_CB3_MachineDigits
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedSplit
open Aeneas Aeneas.Std
open PV_CB3_StagedPacking

def split : Nat → Array U32 8#usize → List U32 × Array U32 8#usize
  | 0, rank => ([],rank)
  | n+1, rank =>
    let first := PV_CB3_StagedMachinePass.pass rank
    let rest := split n first.1
    (first.2 :: rest.1,rest.2)

theorem pass_words (rank : Array U32 8#usize) :
    bits (PV_CB3_StagedMachinePass.pass rank).1 = (PV_CB3_MachinePass.passLE (bits rank)).1 := by
  simp only [PV_CB3_StagedMachinePass.pass,bits_pack]

theorem pass_digit (rank : Array U32 8#usize) :
    (PV_CB3_StagedMachinePass.pass rank).2.bv = (PV_CB3_MachinePass.passLE (bits rank)).2.setWidth 32 := by
  rfl

theorem projection (n : Nat) (rank : Array U32 8#usize) :
    (split n rank).1.map UScalar.bv = (PV_CB3_MachineDigits.split n (bits rank)).1 ∧
    bits (split n rank).2 = (PV_CB3_MachineDigits.split n (bits rank)).2 := by
  induction n generalizing rank with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have tail := ih (PV_CB3_StagedMachinePass.pass rank).1
    dsimp only [split,PV_CB3_MachineDigits.split]
    simp only [List.map_cons,tail.1,tail.2,pass_words,pass_digit]
    simp

theorem length (n : Nat) (rank : Array U32 8#usize) : (split n rank).1.length = n := by
  induction n generalizing rank with
  | zero => rfl
  | succ n ih => simp only [split,List.length_cons,ih]
#print axioms pass_words
#print axioms pass_digit
#print axioms projection
#print axioms length
end R1Z.PV_CB3_StagedSplit
