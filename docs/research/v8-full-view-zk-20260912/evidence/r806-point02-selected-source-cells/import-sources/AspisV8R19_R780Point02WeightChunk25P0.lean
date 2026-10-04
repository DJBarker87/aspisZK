import AspisV8R19.R780Point02WeightShared
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

namespace AspisV8R19.R780Point02WeightChunk25P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
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

theorem pw0_0232 : pw0 232 = 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 232 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather116]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwo 116 (by omega)]
  change 7*w0 (2*116) + 5*(w0 (2*117)) - 5*w0 (2*116+1) = 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_232, w0_leaf_233, w0_leaf_234]
#print axioms pw0_0232

theorem pw0_0233 : pw0 233 = -5*((([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 233 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather116, gather116]
  rw [hwe 116 (by omega), hwe 118 (by omega), hwo 116 (by omega), hwo 117 (by omega)]
  change -5*(w0 (2*116) - (half*w0 (2*116) + half*w0 (2*118))) + 7*w0 (2*116+1) + 5*(w0 (2*117+1)) = -5*((([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod))
  rw [w0_leaf_232, w0_leaf_233, w0_leaf_235, w0_leaf_236]
#print axioms pw0_0233

theorem pw0_0234 : pw0 234 = 7*(([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 234 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather117]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwe 118 (by omega), hwo 117 (by omega)]
  change 7*w0 (2*117) + 5*(half^1*w0 (2*116) + half^1*w0 (2*118)) - 5*w0 (2*117+1) = 7*(([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_232, w0_leaf_234, w0_leaf_235, w0_leaf_236]
#print axioms pw0_0234

theorem pw0_0236 : pw0 236 = 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 236 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather118]
  rw [hwe 118 (by omega), hwe 119 (by omega), hwo 118 (by omega)]
  change 7*w0 (2*118) + 5*(w0 (2*119)) - 5*w0 (2*118+1) = 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_236, w0_leaf_237, w0_leaf_238]
#print axioms pw0_0236

theorem pw0_0237 : pw0 237 = -5*((([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 237 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather118, gather118]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 120 (by omega), hwo 118 (by omega), hwo 119 (by omega)]
  change -5*(w0 (2*118) - (half*w0 (2*118) + half^2*w0 (2*116) + half^3*w0 (2*112) + half^3*w0 (2*120))) + 7*w0 (2*118+1) + 5*(w0 (2*119+1)) = -5*((([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w0_leaf_224, w0_leaf_232, w0_leaf_236, w0_leaf_237, w0_leaf_239, w0_leaf_240]
#print axioms pw0_0237

theorem pw0_0238 : pw0 238 = 7*(([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 238 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather119]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 119 (by omega), hwe 120 (by omega), hwo 119 (by omega)]
  change 7*w0 (2*119) + 5*(half^1*w0 (2*118) + half^2*w0 (2*116) + half^3*w0 (2*112) + half^3*w0 (2*120)) - 5*w0 (2*119+1) = 7*(([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_224, w0_leaf_232, w0_leaf_236, w0_leaf_238, w0_leaf_239, w0_leaf_240]
#print axioms pw0_0238

theorem pw0_0240 : pw0 240 = 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 240 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather120]
  rw [hwe 120 (by omega), hwe 121 (by omega), hwo 120 (by omega)]
  change 7*w0 (2*120) + 5*(w0 (2*121)) - 5*w0 (2*120+1) = 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_240, w0_leaf_241, w0_leaf_242]
#print axioms pw0_0240

theorem pw0_0241 : pw0 241 = -5*((([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 241 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather120, gather120]
  rw [hwe 120 (by omega), hwe 122 (by omega), hwo 120 (by omega), hwo 121 (by omega)]
  change -5*(w0 (2*120) - (half*w0 (2*120) + half*w0 (2*122))) + 7*w0 (2*120+1) + 5*(w0 (2*121+1)) = -5*((([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod))
  rw [w0_leaf_240, w0_leaf_241, w0_leaf_243, w0_leaf_244]
#print axioms pw0_0241

end
end AspisV8R19.R780Point02WeightChunk25P0
