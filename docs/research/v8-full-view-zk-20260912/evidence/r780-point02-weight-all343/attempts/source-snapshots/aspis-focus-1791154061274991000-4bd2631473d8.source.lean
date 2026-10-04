import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R780Point02WeightSharedChunk06
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

namespace AspisV8R19.R780Point02WeightChunk28P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R19.R780Point02WeightSharedChunk06
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

theorem pw2_0265 : pw2 265 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 265 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather132, gather132]
  rw [hwe 132 (by omega), hwe 134 (by omega), hwo 132 (by omega), hwo 133 (by omega)]
  change -5*(w2 (2*132) - (half*w2 (2*132) + half*w2 (2*134))) + 7*w2 (2*132+1) + 5*(w2 (2*133+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_264, w2_leaf_265, w2_leaf_267, w2_leaf_268]
#print axioms pw2_0265

theorem pw2_0267 : pw2 267 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 267 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather133, gather133]
  rw [hwe 133 (by omega), hwe 135 (by omega), hwo 132 (by omega), hwo 133 (by omega), hwo 134 (by omega)]
  change -5*(w2 (2*133) - (half*w2 (2*133) + half*w2 (2*135))) + 7*w2 (2*133+1) + 5*(half^1*w2 (2*132+1) + half^1*w2 (2*134+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_265, w2_leaf_266, w2_leaf_267, w2_leaf_269, w2_leaf_270]
#print axioms pw2_0267

theorem pw2_0268 : pw2 268 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 268 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather134]
  rw [hwe 134 (by omega), hwe 135 (by omega), hwo 134 (by omega)]
  change 7*w2 (2*134) + 5*(w2 (2*135)) - 5*w2 (2*134+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_268, w2_leaf_269, w2_leaf_270]
#print axioms pw2_0268

theorem pw2_0269 : pw2 269 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 269 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather134, gather134]
  rw [hwe 128 (by omega), hwe 132 (by omega), hwe 134 (by omega), hwe 136 (by omega), hwo 134 (by omega), hwo 135 (by omega)]
  change -5*(w2 (2*134) - (half*w2 (2*134) + half^2*w2 (2*132) + half^3*w2 (2*128) + half^3*w2 (2*136))) + 7*w2 (2*134+1) + 5*(w2 (2*135+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_256, w2_leaf_264, w2_leaf_268, w2_leaf_269, w2_leaf_271, w2_leaf_272]
#print axioms pw2_0269

theorem pw2_0271 : pw2 271 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 271 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather135, gather135]
  rw [hwe 129 (by omega), hwe 133 (by omega), hwe 135 (by omega), hwe 137 (by omega), hwo 128 (by omega), hwo 132 (by omega), hwo 134 (by omega), hwo 135 (by omega), hwo 136 (by omega)]
  change -5*(w2 (2*135) - (half*w2 (2*135) + half^2*w2 (2*133) + half^3*w2 (2*129) + half^3*w2 (2*137))) + 7*w2 (2*135+1) + 5*(half^1*w2 (2*134+1) + half^2*w2 (2*132+1) + half^3*w2 (2*128+1) + half^3*w2 (2*136+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0))
  rw [w2_leaf_257, w2_leaf_258, w2_leaf_265, w2_leaf_266, w2_leaf_269, w2_leaf_270, w2_leaf_271, w2_leaf_273, w2_leaf_274]
#print axioms pw2_0271

theorem pw2_0272 : pw2 272 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 272 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather136]
  rw [hwe 136 (by omega), hwe 137 (by omega), hwo 136 (by omega)]
  change 7*w2 (2*136) + 5*(w2 (2*137)) - 5*w2 (2*136+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_272, w2_leaf_273, w2_leaf_274]
#print axioms pw2_0272

theorem pw2_0273 : pw2 273 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 273 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather136, gather136]
  rw [hwe 136 (by omega), hwe 138 (by omega), hwo 136 (by omega), hwo 137 (by omega)]
  change -5*(w2 (2*136) - (half*w2 (2*136) + half*w2 (2*138))) + 7*w2 (2*136+1) + 5*(w2 (2*137+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_272, w2_leaf_273, w2_leaf_275, w2_leaf_276]
#print axioms pw2_0273

theorem pw2_0275 : pw2 275 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 275 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather137, gather137]
  rw [hwe 137 (by omega), hwe 139 (by omega), hwo 136 (by omega), hwo 137 (by omega), hwo 138 (by omega)]
  change -5*(w2 (2*137) - (half*w2 (2*137) + half*w2 (2*139))) + 7*w2 (2*137+1) + 5*(half^1*w2 (2*136+1) + half^1*w2 (2*138+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_273, w2_leaf_274, w2_leaf_275, w2_leaf_277, w2_leaf_278]
#print axioms pw2_0275

end
end AspisV8R19.R780Point02WeightChunk28P2
