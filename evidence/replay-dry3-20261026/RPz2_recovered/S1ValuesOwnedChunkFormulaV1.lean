import S1ValuesOwnedCellV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedChunkFormula
open Aeneas Aeneas.Std Result
abbrev Buffer := alloc.vec.Vec U8

def Written (chunk byte j : Nat) : Prop :=
  (chunk*32 ≤ j ∧ j<chunk*32+byte) ∨
  (chunk*32+16 ≤ j ∧ j<chunk*32+16+byte)
instance (chunk byte j : Nat) : Decidable (Written chunk byte j) := by
  unfold Written
  infer_instance

def Desired (input : Buffer) (chunk j : Nat) : Option U8 :=
  if j<chunk*32+16 then input.val[chunk*16+(j-chunk*32)]? else some 0#u8

def Partial (input original output : Buffer) (chunk byte : Nat) : Prop :=
  ∀ j, output.val[j]?=if Written chunk byte j then Desired input chunk j else original.val[j]?

theorem initial (input output : Buffer) (chunk : Nat) : Partial input output output chunk 0 := by
  intro j
  have empty : ¬Written chunk 0 j := by unfold Written;omega
  simp only [if_neg empty]

/-- Pure pointwise composition of the actual low-limb write followed by its
high-limb zero write. No buffer content is enumerated. -/
theorem advance (input original output updated : Buffer) (chunk byte : Nat)
    (active : byte<16) (held : Partial input original output chunk byte)
    (writes : ∀ j, updated.val[j]?=
      if j=chunk*32+16+byte then some 0#u8
      else if j=chunk*32+byte then input.val[chunk*16+byte]? else output.val[j]?) :
    Partial input original updated chunk (byte+1) := by
  intro j
  rw [writes j,held j]
  by_cases high : j=chunk*32+16+byte
  · have low : j≠chunk*32+byte := by omega
    have written : Written chunk (byte+1) j := by unfold Written;omega
    have select : ¬j<chunk*32+16 := by omega
    simp only [if_pos high,if_pos written,Desired,if_neg select]
  · by_cases low : j=chunk*32+byte
    · have written : Written chunk (byte+1) j := by unfold Written;omega
      have select : j<chunk*32+16 := by omega
      have address : chunk*16+(j-chunk*32)=chunk*16+byte := by omega
      simp only [if_neg high,if_pos low,if_pos written,Desired,if_pos select,address]
    · have unchanged : Written chunk (byte+1) j ↔ Written chunk byte j := by
        unfold Written
        omega
      simp only [if_neg high,if_neg low,unchanged]

#print axioms initial
#print axioms advance
end AspisS1ValuesOwnedChunkFormula
