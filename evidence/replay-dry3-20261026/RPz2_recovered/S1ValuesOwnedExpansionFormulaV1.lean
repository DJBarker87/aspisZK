import S1ValuesOwnedChunkBytesV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedExpansionFormula
open Aeneas Aeneas.Std Result
open AspisS1ValuesOwnedChunkFormula

def Desired (input : Buffer) (j : Nat) : Option U8 :=
  if j%32<16 then input.val[(j/32)*16+j%32]? else some 0#u8

def Partial (input original output : Buffer) (chunk : Nat) : Prop :=
  ∀ j, output.val[j]?=if j<chunk*32 then Desired input j else original.val[j]?

theorem initial (input output : Buffer) : Partial input output output 0 := by
  intro j
  simp only [Nat.zero_mul,Nat.not_lt_zero,ite_false]

theorem desired_chunk (input : Buffer) (chunk j : Nat)
    (lower : chunk*32 ≤ j) (upper : j<chunk*32+32) :
    AspisS1ValuesOwnedChunkFormula.Desired input chunk j=Desired input j := by
  have quotient : j/32=chunk := by omega
  have remainder : j%32=j-chunk*32 := by omega
  by_cases low : j<chunk*32+16
  · have lane : j%32<16 := by omega
    unfold AspisS1ValuesOwnedChunkFormula.Desired Desired
    rw [if_pos low,if_pos lane,quotient,remainder]
  · have lane : ¬j%32<16 := by omega
    simp only [AspisS1ValuesOwnedChunkFormula.Desired,Desired,if_neg low,if_neg lane]

theorem chunk_update (input original updated : Buffer) (chunk : Nat)
    (held : AspisS1ValuesOwnedChunkFormula.Partial input original updated chunk 16) (j : Nat) :
    updated.val[j]?=if chunk*32 ≤ j ∧ j<chunk*32+32 then Desired input j else original.val[j]? := by
  have full : Written chunk 16 j ↔ chunk*32 ≤ j ∧ j<chunk*32+32 := by unfold Written;omega
  rw [held j]
  simp only [full]
  by_cases inside : chunk*32 ≤ j ∧ j<chunk*32+32
  · simp only [if_pos inside]
    exact desired_chunk input chunk j inside.1 inside.2
  · simp only [if_neg inside]

theorem advance (input original output updated : Buffer) (chunk : Nat)
    (held : Partial input original output chunk)
    (step : AspisS1ValuesOwnedChunkFormula.Partial input output updated chunk 16) :
    Partial input original updated (chunk+1) := by
  intro j
  rw [chunk_update input output updated chunk step j,held j]
  by_cases inside : chunk*32 ≤ j ∧ j<chunk*32+32
  · have completed : j<(chunk+1)*32 := by omega
    simp only [if_pos inside,if_pos completed]
  · have same : j<(chunk+1)*32 ↔ j<chunk*32 := by omega
    simp only [if_neg inside,same]

#print axioms desired_chunk
#print axioms chunk_update
#print axioms advance
end AspisS1ValuesOwnedExpansionFormula
