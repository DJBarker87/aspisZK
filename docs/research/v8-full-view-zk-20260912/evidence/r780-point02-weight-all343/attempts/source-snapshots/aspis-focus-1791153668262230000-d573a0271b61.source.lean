import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk04
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

namespace AspisV8R19.R780Point02WeightChunk24P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk04
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

theorem pw0_0226 : pw0 226 = 7*(([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 226 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather113]
  rw [hwe 112 (by omega), hwe 113 (by omega), hwe 114 (by omega), hwo 113 (by omega)]
  change 7*w0 (2*113) + 5*(half^1*w0 (2*112) + half^1*w0 (2*114)) - 5*w0 (2*113+1) = 7*(([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_224, w0_leaf_226, w0_leaf_227, w0_leaf_228]
#print axioms pw0_0226

theorem pw0_0228 : pw0 228 = 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 228 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather114]
  rw [hwe 114 (by omega), hwe 115 (by omega), hwo 114 (by omega)]
  change 7*w0 (2*114) + 5*(w0 (2*115)) - 5*w0 (2*114+1) = 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_228, w0_leaf_229, w0_leaf_230]
#print axioms pw0_0228

theorem pw0_0229 : pw0 229 = -5*((([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 229 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather114, gather114]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwe 116 (by omega), hwo 114 (by omega), hwo 115 (by omega)]
  change -5*(w0 (2*114) - (half*w0 (2*114) + half^2*w0 (2*112) + half^2*w0 (2*116))) + 7*w0 (2*114+1) + 5*(w0 (2*115+1)) = -5*((([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w0_leaf_224, w0_leaf_228, w0_leaf_229, w0_leaf_231, w0_leaf_232]
#print axioms pw0_0229

theorem pw0_0230 : pw0 230 = 7*(([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 230 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather115]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwe 115 (by omega), hwe 116 (by omega), hwo 115 (by omega)]
  change 7*w0 (2*115) + 5*(half^1*w0 (2*114) + half^2*w0 (2*112) + half^2*w0 (2*116)) - 5*w0 (2*115+1) = 7*(([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_224, w0_leaf_228, w0_leaf_230, w0_leaf_231, w0_leaf_232]
#print axioms pw0_0230

end
end AspisV8R19.R780Point02WeightChunk24P0
