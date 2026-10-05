import AspisV8R19.R861SemanticMaskFinishCoins
import AspisV8R19.R787PairSupportZero
import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R15.ExactTowerBase
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R864SemanticKernel
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R773LowActiveKernel
open AspisV8R15.ExactTowerBase
open scoped BigOperators
noncomputable section
abbrev M := ZMod 2147483647
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact

def halfSelected : M := 1073741824
def alphaSelected : M := 7
def z : Fin 10 → M := ![1,1,2,3,4,2,2,3,0,2]
def semanticZ : RoundCoins M 10 :=
  (1, (1, (2, (3, (4, (2, (2, (3, (0, (2, PUnit.unit))))))))))
def d96 : Fin 255 := ⟨96, by decide⟩
def s0 : Fin 3 := ⟨0, by decide⟩
def q : Nat → M := direction alphaSelected d96 s0

lemma loop0 : indexLoop 10 0 0 = some [(1,0)] := by rfl
lemma loop1 : indexLoop 10 1 0 = some [(0,1),(2,1)] := by rfl
lemma loop192 : indexLoop 10 192 0 = some [(193,0)] := by rfl
lemma loop193 : indexLoop 10 193 0 = some [(192,1),(194,1)] := by rfl

lemma sparseX0 (r : Nat) : sparseX halfSelected 0 r = unitVector 1 r := by
  unfold sparseX sparseVector
  change (List.map (fun e : Nat × M => if r = e.1 then e.2 else 0)
    ((weightedIndexLoop halfSelected 10 0 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop0]
  simp [unitVector]

lemma sparseX192 (r : Nat) : sparseX halfSelected 192 r = unitVector 193 r := by
  unfold sparseX sparseVector
  change (List.map (fun e : Nat × M => if r = e.1 then e.2 else 0)
    ((weightedIndexLoop halfSelected 10 192 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop192]
  simp [unitVector]

lemma sparseX1 (r : Nat) :
    sparseX halfSelected 1 r = halfSelected * unitVector 0 r + halfSelected * unitVector 2 r := by
  unfold sparseX sparseVector
  change (List.map (fun e : Nat × M => if r = e.1 then e.2 else 0)
    ((weightedIndexLoop halfSelected 10 1 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop1]
  simp [unitVector]

lemma sparseX193 (r : Nat) :
    sparseX halfSelected 193 r = halfSelected * unitVector 192 r + halfSelected * unitVector 194 r := by
  unfold sparseX sparseVector
  change (List.map (fun e : Nat × M => if r = e.1 then e.2 else 0)
    ((weightedIndexLoop halfSelected 10 193 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop193]
  simp [unitVector]

lemma sparseXX0 (r : Nat) :
    sparseXX halfSelected 0 r = halfSelected * unitVector 0 r + halfSelected * unitVector 2 r := by
  unfold sparseXX
  change (List.map (fun e : Nat × M => e.2 * sparseX halfSelected e.1 r)
    ((weightedIndexLoop halfSelected 10 0 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop0]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  simp only [Option.getD_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  exact sparseX1 r

lemma sparseXX192 (r : Nat) :
    sparseXX halfSelected 192 r = halfSelected * unitVector 192 r + halfSelected * unitVector 194 r := by
  unfold sparseXX
  change (List.map (fun e : Nat × M => e.2 * sparseX halfSelected e.1 r)
    ((weightedIndexLoop halfSelected 10 192 0 (halfSelected^(0:Nat))).getD [])).sum = _
  rw [weightedIndexLoop_powers, loop192]
  simp only [Option.map_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  simp only [Option.getD_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, one_mul]
  exact sparseX193 r

lemma q_expansion : q = fun r => unitVector 385 r - 7*unitVector 384 r - unitVector 1 r + 7*unitVector 0 r := by
  funext r
  simp [q, direction, qPair, alphaSelected, d96, s0]
  ring

lemma chord_at_386 :
    sourceChord halfSelected q (7:M) 5 (-5) 386 = -35 := by
  have h385 : sourceChord halfSelected (unitVector 385) (7:M) 5 (-5) 386 = 0 := by
    rw [sourceChord_unit_odd halfSelected 192 386 (by decide) (7:M) 5 (-5)]
    rw [sparseXX192]
    norm_num [unitVector]
  have h384 : sourceChord halfSelected (unitVector 384) (7:M) 5 (-5) 386 = 5 := by
    rw [sourceChord_unit_even halfSelected 192 386 (by decide) (7:M) 5 (-5)]
    rw [sparseX192]
    norm_num [unitVector]
  have h1 : sourceChord halfSelected (unitVector 1) (7:M) 5 (-5) 386 = 0 := by
    exact sourceChord_unit_low_zero halfSelected (7:M) 5 (-5) ⟨1, by decide⟩ 386 (by decide)
  have h0 : sourceChord halfSelected (unitVector 0) (7:M) 5 (-5) 386 = 0 := by
    exact sourceChord_unit_low_zero halfSelected (7:M) 5 (-5) ⟨0, by decide⟩ 386 (by decide)
  let qhigh : Nat → M := fun r => unitVector 385 r - (7:M)*unitVector 384 r
  let qlow : Nat → M := fun r => unitVector 1 r - (7:M)*unitVector 0 r
  have hq : q = fun r => qhigh r - qlow r := by
    funext r
    simp [qhigh, qlow, q_expansion]
    ring
  rw [hq]
  have hdifflow := sourceChord_difference halfSelected qhigh qlow (7:M) 5 (-5) (1:M) 386
  simp only [one_mul] at hdifflow
  rw [hdifflow]
  have hh : sourceChord halfSelected qhigh (7:M) 5 (-5) 386 = -35 := by
    dsimp [qhigh]
    rw [sourceChord_difference halfSelected (unitVector 385) (unitVector 384)
      (7:M) 5 (-5) 7 386, h385, h384]
    norm_num
  have hl : sourceChord halfSelected qlow (7:M) 5 (-5) 386 = 0 := by
    dsimp [qlow]
    rw [sourceChord_difference halfSelected (unitVector 1) (unitVector 0)
      (7:M) 5 (-5) 7 386, h1, h0]
    norm_num
  rw [hh, hl]
  norm_num

lemma non86_pair_absent (i : Fin 271) (hi : i.val ≠ 86) :
    ¬ pairSupport d96 s0 (128 + 3*i.val) := by
  simp only [pairSupport, s0]
  change ¬ (evenUnitSupport 192 (128 + 3*i.val) ∨ oddUnitSupport 192 (128 + 3*i.val))
  simp only [evenUnitSupport, oddUnitSupport]
  rw [show indexTargets 192 = [193] by
      unfold indexTargets
      rw [loop192]
      rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show indexTargets 193 = [192,194] by
      unfold indexTargets
      rw [loop193]
      rfl]
  simp
  constructor
  · constructor
    · intro h
      omega
    · intro hp h
      omega
  · constructor
    · intro h
      omega
    · split <;> intro h <;> omega

lemma chord_at_other_coin_zero (i : Fin 271) (hi : i.val ≠ 86) :
    sourceChord halfSelected q (7:M) 5 (-5) (128 + 3*i.val) = 0 := by
  exact direction_sourceChord_zero_of_not_pairSupport halfSelected alphaSelected (7:M) 5 (-5)
    d96 s0 (128+3*i.val) (by have := i.isLt; omega) (non86_pair_absent i hi)

lemma mask_weight_86 :
    maskWeights271 halfSelected semanticZ ⟨86, by decide⟩ = (15 : M) / (4 : M) := by
  simp [maskWeights271, listAsFin, flatMaskWeights, reverseWeightBlocks,
    roundWeightBlock, semanticZ]
  have htwo : (2 : M) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    change ((2 : M).val) = 0 at hh
    have hval : (2 : M).val = 2 := by
      change 2 % 2147483647 = 2
      norm_num
    rw [hval] at hh
    omega
  have hhalf : halfSelected = (1 : M) / 2 := by
    apply (eq_div_iff htwo).2
    have hnat : 1073741824 * 2 = 2147483647 + 1 := by norm_num
    change ((1073741824 : Nat) : M) * ((2 : Nat) : M) = (1 : M)
    rw [← Nat.cast_mul, hnat, Nat.cast_add, ZMod.natCast_self]
    norm_num
  rw [hhalf]
  have hfour : (4 : M) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    change ((4 : M).val) = 0 at hh
    have hval : (4 : M).val = 4 := by
      change 4 % 2147483647 = 4
      norm_num
    rw [hval] at hh
    omega
  apply (eq_div_iff hfour).2
  field_simp [htwo]
  ring

lemma semantic_pairing :
    (∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      sourceChord halfSelected q (7:M) 5 (-5) (128 + 3*i.val)) =
      (1610612604 : M) := by
  classical
  let i86 : Fin 271 := ⟨86, by decide⟩
  rw [Finset.sum_eq_single i86]
  · rw [mask_weight_86]
    change (15 : M) / 4 * sourceChord halfSelected q (7:M) 5 (-5) 386 =
      (1610612604 : M)
    rw [chord_at_386]
    rw [div_mul_eq_mul_div]
    have hfour : (4 : M) ≠ 0 := by
      intro h
      have hh := congrArg ZMod.val h
      change ((4 : M).val) = 0 at hh
      have hval : (4 : M).val = 4 := by
        change 4 % 2147483647 = 4
        norm_num
      rw [hval] at hh
      omega
    apply (div_eq_iff hfour).2
    have hnat : 1610612604 * 4 + 525 = 3 * 2147483647 := by norm_num
    have hzero : (1610612604 : M) * 4 + 525 = 0 := by
      change ((1610612604 * 4 + 525 : Nat) : M) = 0
      rw [hnat, Nat.cast_mul, ZMod.natCast_self, mul_zero]
    linear_combination -hzero
  · intro i _ hi
    have hne : i.val ≠ 86 := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    rw [chord_at_other_coin_zero i hne, mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_univ i86)

#print axioms loop0
#print axioms loop1
#print axioms loop192
#print axioms loop193
#print axioms sparseX0
#print axioms sparseX192
#print axioms sparseX1
#print axioms sparseX193
#print axioms sparseXX0
#print axioms sparseXX192
#print axioms chord_at_386
#print axioms non86_pair_absent
#print axioms chord_at_other_coin_zero
#print axioms mask_weight_86
#print axioms semantic_pairing
end
end AspisV8R19.R864SemanticKernel
