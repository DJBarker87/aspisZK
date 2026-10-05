import AspisV8R19.R861SemanticMaskFinishCoins
import AspisV8R19.R787PairSupportZero
import AspisV8R19.R775GatherUnitChordBridge
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R864SemanticKernel
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R787PairSupportZero
noncomputable section
abbrev M := ZMod 2147483647

def halfSelected : M := 1073741824
def alphaSelected : M := 7
def z : Fin 10 → M := ![1,1,2,3,4,2,2,3,0,2]
def d96 : Fin 255 := ⟨96, by decide⟩
def s0 : Fin 3 := ⟨0, by decide⟩
def q : Nat → M := direction alphaSelected d96 s0

lemma loop0 : indexLoop 10 0 0 = some [(1,0)] := by rfl
lemma loop1 : indexLoop 10 1 0 = some [(0,1),(2,1)] := by rfl
lemma loop192 : indexLoop 10 192 0 = some [(193,0)] := by rfl
lemma loop193 : indexLoop 10 193 0 = some [(192,1),(194,1)] := by rfl

lemma sparseX0 (r : Nat) : sparseX halfSelected 0 r = unitVector 1 r := by
  unfold sparseX sparseVector
  rw [weightedIndexLoop_powers, loop0]
  norm_num

lemma sparseX192 (r : Nat) : sparseX halfSelected 192 r = unitVector 193 r := by
  unfold sparseX sparseVector
  rw [weightedIndexLoop_powers, loop192]
  norm_num

lemma sparseXX0 (r : Nat) :
    sparseXX halfSelected 0 r = halfSelected * unitVector 0 r + halfSelected * unitVector 2 r := by
  unfold sparseXX
  rw [weightedIndexLoop_powers, loop0]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  rw [sparseX0, show (1:M) = halfSelected^0 by norm_num]
  unfold sparseX sparseVector
  rw [weightedIndexLoop_powers, loop1]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

lemma sparseXX192 (r : Nat) :
    sparseXX halfSelected 192 r = halfSelected * unitVector 192 r + halfSelected * unitVector 194 r := by
  unfold sparseXX
  rw [weightedIndexLoop_powers, loop192]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  rw [sparseX192, show (1:M) = halfSelected^0 by norm_num]
  unfold sparseX sparseVector
  rw [weightedIndexLoop_powers, loop193]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

lemma q_expansion : q = fun r => unitVector 385 r - 7*unitVector 384 r - unitVector 1 r + 7*unitVector 0 r := by
  funext r
  simp [q, direction, qPair, alphaSelected, d96, s0]
  ring

lemma chord_at_386 :
    sourceChord halfSelected q (7:M) 5 (-5) 386 = -35 := by
  rw [q_expansion]
  -- isolate the four source units; their only live contribution at 386 is the even unit 384.
  sorry

#print axioms loop0
#print axioms loop1
#print axioms loop192
#print axioms loop193
#print axioms sparseX0
#print axioms sparseX192
#print axioms sparseXX0
#print axioms sparseXX192
end
end AspisV8R19.R864SemanticKernel
