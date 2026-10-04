import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R748SchedulePrototype
import AspisV8R19.R748GatherLoop00
import AspisV8R19.R748GatherLoop01
import AspisV8R19.R748GatherLoop02
import AspisV8R19.R748GatherLoop03
import AspisV8R19.R748GatherLoop04
import AspisV8R19.R748GatherLoop05
import AspisV8R19.R748GatherLoop06
import AspisV8R19.R748GatherLoop07
import AspisV8R19.R748GatherExpand00
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherExpand03
import AspisV8R19.R748GatherExpand04
import AspisV8R19.R748GatherExpand05
import AspisV8R19.R748GatherExpand06
import AspisV8R19.R748GatherExpand07
import AspisV8R19.R748GatherNested00
import AspisV8R19.R748GatherNested01
import AspisV8R19.R748GatherNested02
import AspisV8R19.R748GatherNested03
import AspisV8R19.R748GatherNested04

namespace AspisV8R19.R780Point02WeightChunk26P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R17
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R748FiniteGatherSchedules
open AspisV8R19.R748SchedulePrototype
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherExpand03
open AspisV8R19.R748GatherExpand04
open AspisV8R19.R748GatherExpand05
open AspisV8R19.R748GatherExpand06
open AspisV8R19.R748GatherExpand07
open AspisV8R19.R748GatherNested00
open AspisV8R19.R748GatherNested01
open AspisV8R19.R748GatherNested02
open AspisV8R19.R748GatherNested03
open AspisV8R19.R748GatherNested04
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096

theorem pw2_0243 : pw2 243 = -5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 243 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather121, gather121]
  rw [hwe 121 (by omega), hwe 123 (by omega), hwo 120 (by omega), hwo 121 (by omega), hwo 122 (by omega)]
  change -5*(w2 (2*121) - (half*w2 (2*121) + half*w2 (2*123))) + 7*w2 (2*121+1) + 5*(half^1*w2 (2*120+1) + half^1*w2 (2*122+1)) = -5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_241, w2_leaf_242, w2_leaf_243, w2_leaf_245, w2_leaf_246]
#print axioms pw2_0243

theorem pw2_0244 : pw2 244 = 7*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 244 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather122]
  rw [hwe 122 (by omega), hwe 123 (by omega), hwo 122 (by omega)]
  change 7*w2 (2*122) + 5*(w2 (2*123)) - 5*w2 (2*122+1) = 7*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_244, w2_leaf_245, w2_leaf_246]
#print axioms pw2_0244

theorem pw2_0245 : pw2 245 = -5*((([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 245 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather122, gather122]
  rw [hwe 120 (by omega), hwe 122 (by omega), hwe 124 (by omega), hwo 122 (by omega), hwo 123 (by omega)]
  change -5*(w2 (2*122) - (half*w2 (2*122) + half^2*w2 (2*120) + half^2*w2 (2*124))) + 7*w2 (2*122+1) + 5*(w2 (2*123+1)) = -5*((([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_240, w2_leaf_244, w2_leaf_245, w2_leaf_247, w2_leaf_248]
#print axioms pw2_0245

theorem pw2_0247 : pw2 247 = -5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 247 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather123, gather123]
  rw [hwe 121 (by omega), hwe 123 (by omega), hwe 125 (by omega), hwo 120 (by omega), hwo 122 (by omega), hwo 123 (by omega), hwo 124 (by omega)]
  change -5*(w2 (2*123) - (half*w2 (2*123) + half^2*w2 (2*121) + half^2*w2 (2*125))) + 7*w2 (2*123+1) + 5*(half^1*w2 (2*122+1) + half^2*w2 (2*120+1) + half^2*w2 (2*124+1)) = -5*((([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_241, w2_leaf_242, w2_leaf_245, w2_leaf_246, w2_leaf_247, w2_leaf_249, w2_leaf_250]
#print axioms pw2_0247

theorem pw2_0248 : pw2 248 = 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 248 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather124]
  rw [hwe 124 (by omega), hwe 125 (by omega), hwo 124 (by omega)]
  change 7*w2 (2*124) + 5*(w2 (2*125)) - 5*w2 (2*124+1) = 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_248, w2_leaf_249, w2_leaf_250]
#print axioms pw2_0248

theorem pw2_0249 : pw2 249 = -5*((([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 249 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather124, gather124]
  rw [hwe 124 (by omega), hwe 126 (by omega), hwo 124 (by omega), hwo 125 (by omega)]
  change -5*(w2 (2*124) - (half*w2 (2*124) + half*w2 (2*126))) + 7*w2 (2*124+1) + 5*(w2 (2*125+1)) = -5*((([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_248, w2_leaf_249, w2_leaf_251, w2_leaf_252]
#print axioms pw2_0249

theorem pw2_0251 : pw2 251 = -5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 251 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather125, gather125]
  rw [hwe 125 (by omega), hwe 127 (by omega), hwo 124 (by omega), hwo 125 (by omega), hwo 126 (by omega)]
  change -5*(w2 (2*125) - (half*w2 (2*125) + half*w2 (2*127))) + 7*w2 (2*125+1) + 5*(half^1*w2 (2*124+1) + half^1*w2 (2*126+1)) = -5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_249, w2_leaf_250, w2_leaf_251, w2_leaf_253, w2_leaf_254]
#print axioms pw2_0251

theorem pw2_0252 : pw2 252 = 7*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 252 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather126]
  rw [hwe 126 (by omega), hwe 127 (by omega), hwo 126 (by omega)]
  change 7*w2 (2*126) + 5*(w2 (2*127)) - 5*w2 (2*126+1) = 7*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_252, w2_leaf_253, w2_leaf_254]
#print axioms pw2_0252

end
end AspisV8R19.R780Point02WeightChunk26P2
