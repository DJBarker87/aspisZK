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

namespace AspisV8R19.R780Point02WeightChunk25P2
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

theorem pw2_0232 : pw2 232 = 7*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 232 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather116]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwo 116 (by omega)]
  change 7*w2 (2*116) + 5*(w2 (2*117)) - 5*w2 (2*116+1) = 7*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_232, w2_leaf_233, w2_leaf_234]
#print axioms pw2_0232

theorem pw2_0233 : pw2 233 = -5*((([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 233 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather116, gather116]
  rw [hwe 116 (by omega), hwe 118 (by omega), hwo 116 (by omega), hwo 117 (by omega)]
  change -5*(w2 (2*116) - (half*w2 (2*116) + half*w2 (2*118))) + 7*w2 (2*116+1) + 5*(w2 (2*117+1)) = -5*((([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_232, w2_leaf_233, w2_leaf_235, w2_leaf_236]
#print axioms pw2_0233

theorem pw2_0234 : pw2 234 = 7*(([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 234 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather117]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwe 118 (by omega), hwo 117 (by omega)]
  change 7*w2 (2*117) + 5*(half^1*w2 (2*116) + half^1*w2 (2*118)) - 5*w2 (2*117+1) = 7*(([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_232, w2_leaf_234, w2_leaf_235, w2_leaf_236]
#print axioms pw2_0234

theorem pw2_0236 : pw2 236 = 7*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 236 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather118]
  rw [hwe 118 (by omega), hwe 119 (by omega), hwo 118 (by omega)]
  change 7*w2 (2*118) + 5*(w2 (2*119)) - 5*w2 (2*118+1) = 7*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_236, w2_leaf_237, w2_leaf_238]
#print axioms pw2_0236

theorem pw2_0237 : pw2 237 = -5*((([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 237 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather118, gather118]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 120 (by omega), hwo 118 (by omega), hwo 119 (by omega)]
  change -5*(w2 (2*118) - (half*w2 (2*118) + half^2*w2 (2*116) + half^3*w2 (2*112) + half^3*w2 (2*120))) + 7*w2 (2*118+1) + 5*(w2 (2*119+1)) = -5*((([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_224, w2_leaf_232, w2_leaf_236, w2_leaf_237, w2_leaf_239, w2_leaf_240]
#print axioms pw2_0237

theorem pw2_0238 : pw2 238 = 7*(([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 238 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather119]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 119 (by omega), hwe 120 (by omega), hwo 119 (by omega)]
  change 7*w2 (2*119) + 5*(half^1*w2 (2*118) + half^2*w2 (2*116) + half^3*w2 (2*112) + half^3*w2 (2*120)) - 5*w2 (2*119+1) = 7*(([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_224, w2_leaf_232, w2_leaf_236, w2_leaf_238, w2_leaf_239, w2_leaf_240]
#print axioms pw2_0238

theorem pw2_0240 : pw2 240 = 7*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 240 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather120]
  rw [hwe 120 (by omega), hwe 121 (by omega), hwo 120 (by omega)]
  change 7*w2 (2*120) + 5*(w2 (2*121)) - 5*w2 (2*120+1) = 7*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod)
  rw [w2_leaf_240, w2_leaf_241, w2_leaf_242]
#print axioms pw2_0240

theorem pw2_0241 : pw2 241 = -5*((([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 241 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather120, gather120]
  rw [hwe 120 (by omega), hwe 122 (by omega), hwo 120 (by omega), hwo 121 (by omega)]
  change -5*(w2 (2*120) - (half*w2 (2*120) + half*w2 (2*122))) + 7*w2 (2*120+1) + 5*(w2 (2*121+1)) = -5*((([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod))
  rw [w2_leaf_240, w2_leaf_241, w2_leaf_243, w2_leaf_244]
#print axioms pw2_0241

end
end AspisV8R19.R780Point02WeightChunk25P2
