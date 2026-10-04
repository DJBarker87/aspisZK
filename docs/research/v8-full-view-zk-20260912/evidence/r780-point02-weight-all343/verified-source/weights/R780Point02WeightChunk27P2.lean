import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk00
import AspisV8R19.R780Point02WeightSharedChunk01
import AspisV8R19.R780Point02WeightSharedChunk03
import AspisV8R19.R780Point02WeightSharedChunk04
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

namespace AspisV8R19.R780Point02WeightChunk27P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk00
open AspisV8R19.R780Point02WeightSharedChunk01
open AspisV8R19.R780Point02WeightSharedChunk03
open AspisV8R19.R780Point02WeightSharedChunk04
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

theorem pw2_0253 : pw2 253 = -5*((([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0))) + 7*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 253 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather126, gather126]
  rw [hwe 0 (by omega), hwe 64 (by omega), hwe 96 (by omega), hwe 112 (by omega), hwe 120 (by omega), hwe 124 (by omega), hwe 126 (by omega), hwe 128 (by omega), hwo 126 (by omega), hwo 127 (by omega)]
  change -5*(w2 (2*126) - (half*w2 (2*126) + half^2*w2 (2*124) + half^3*w2 (2*120) + half^4*w2 (2*112) + half^5*w2 (2*96) + half^6*w2 (2*64) + half^7*w2 (2*0) + half^7*w2 (2*128))) + 7*w2 (2*126+1) + 5*(w2 (2*127+1)) = -5*((([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0))) + 7*(([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_0, w2_leaf_128, w2_leaf_192, w2_leaf_224, w2_leaf_240, w2_leaf_248, w2_leaf_252, w2_leaf_253, w2_leaf_255, w2_leaf_256]
#print axioms pw2_0253

theorem pw2_0256 : pw2 256 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 256 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather128]
  rw [hwe 128 (by omega), hwe 129 (by omega), hwo 128 (by omega)]
  change 7*w2 (2*128) + 5*(w2 (2*129)) - 5*w2 (2*128+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_256, w2_leaf_257, w2_leaf_258]
#print axioms pw2_0256

theorem pw2_0257 : pw2 257 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 257 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather128, gather128]
  rw [hwe 128 (by omega), hwe 130 (by omega), hwo 128 (by omega), hwo 129 (by omega)]
  change -5*(w2 (2*128) - (half*w2 (2*128) + half*w2 (2*130))) + 7*w2 (2*128+1) + 5*(w2 (2*129+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_256, w2_leaf_257, w2_leaf_259, w2_leaf_260]
#print axioms pw2_0257

theorem pw2_0259 : pw2 259 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 259 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather129, gather129]
  rw [hwe 129 (by omega), hwe 131 (by omega), hwo 128 (by omega), hwo 129 (by omega), hwo 130 (by omega)]
  change -5*(w2 (2*129) - (half*w2 (2*129) + half*w2 (2*131))) + 7*w2 (2*129+1) + 5*(half^1*w2 (2*128+1) + half^1*w2 (2*130+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_257, w2_leaf_258, w2_leaf_259, w2_leaf_261, w2_leaf_262]
#print axioms pw2_0259

theorem pw2_0260 : pw2 260 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 260 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather130]
  rw [hwe 130 (by omega), hwe 131 (by omega), hwo 130 (by omega)]
  change 7*w2 (2*130) + 5*(w2 (2*131)) - 5*w2 (2*130+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_260, w2_leaf_261, w2_leaf_262]
#print axioms pw2_0260

theorem pw2_0261 : pw2 261 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 261 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather130, gather130]
  rw [hwe 128 (by omega), hwe 130 (by omega), hwe 132 (by omega), hwo 130 (by omega), hwo 131 (by omega)]
  change -5*(w2 (2*130) - (half*w2 (2*130) + half^2*w2 (2*128) + half^2*w2 (2*132))) + 7*w2 (2*130+1) + 5*(w2 (2*131+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_256, w2_leaf_260, w2_leaf_261, w2_leaf_263, w2_leaf_264]
#print axioms pw2_0261

theorem pw2_0263 : pw2 263 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 263 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather131, gather131]
  rw [hwe 129 (by omega), hwe 131 (by omega), hwe 133 (by omega), hwo 128 (by omega), hwo 130 (by omega), hwo 131 (by omega), hwo 132 (by omega)]
  change -5*(w2 (2*131) - (half*w2 (2*131) + half^2*w2 (2*129) + half^2*w2 (2*133))) + 7*w2 (2*131+1) + 5*(half^1*w2 (2*130+1) + half^2*w2 (2*128+1) + half^2*w2 (2*132+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w2_leaf_257, w2_leaf_258, w2_leaf_261, w2_leaf_262, w2_leaf_263, w2_leaf_265, w2_leaf_266]
#print axioms pw2_0263

theorem pw2_0264 : pw2 264 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 264 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather132]
  rw [hwe 132 (by omega), hwe 133 (by omega), hwo 132 (by omega)]
  change 7*w2 (2*132) + 5*(w2 (2*133)) - 5*w2 (2*132+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_264, w2_leaf_265, w2_leaf_266]
#print axioms pw2_0264

end
end AspisV8R19.R780Point02WeightChunk27P2
