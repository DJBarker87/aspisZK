import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk08
import AspisV8R19.R780Point02WeightSharedChunk09
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

namespace AspisV8R19.R780Point02WeightChunk37P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk08
open AspisV8R19.R780Point02WeightSharedChunk09
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

theorem pw0_0364 : pw0 364 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 364 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather182]
  rw [hwe 182 (by omega), hwe 183 (by omega), hwo 182 (by omega)]
  change 7*w0 (2*182) + 5*(w0 (2*183)) - 5*w0 (2*182+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_364, w0_leaf_365, w0_leaf_366]
#print axioms pw0_0364

theorem pw0_0365 : pw0 365 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 365 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather182, gather182]
  rw [hwe 176 (by omega), hwe 180 (by omega), hwe 182 (by omega), hwe 184 (by omega), hwo 182 (by omega), hwo 183 (by omega)]
  change -5*(w0 (2*182) - (half*w0 (2*182) + half^2*w0 (2*180) + half^3*w0 (2*176) + half^3*w0 (2*184))) + 7*w0 (2*182+1) + 5*(w0 (2*183+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_352, w0_leaf_360, w0_leaf_364, w0_leaf_365, w0_leaf_367, w0_leaf_368]
#print axioms pw0_0365

theorem pw0_0367 : pw0 367 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 367 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather183, gather183]
  rw [hwe 177 (by omega), hwe 181 (by omega), hwe 183 (by omega), hwe 185 (by omega), hwo 176 (by omega), hwo 180 (by omega), hwo 182 (by omega), hwo 183 (by omega), hwo 184 (by omega)]
  change -5*(w0 (2*183) - (half*w0 (2*183) + half^2*w0 (2*181) + half^3*w0 (2*177) + half^3*w0 (2*185))) + 7*w0 (2*183+1) + 5*(half^1*w0 (2*182+1) + half^2*w0 (2*180+1) + half^3*w0 (2*176+1) + half^3*w0 (2*184+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0))
  rw [w0_leaf_353, w0_leaf_354, w0_leaf_361, w0_leaf_362, w0_leaf_365, w0_leaf_366, w0_leaf_367, w0_leaf_369, w0_leaf_370]
#print axioms pw0_0367

theorem pw0_0368 : pw0 368 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 368 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather184]
  rw [hwe 184 (by omega), hwe 185 (by omega), hwo 184 (by omega)]
  change 7*w0 (2*184) + 5*(w0 (2*185)) - 5*w0 (2*184+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_368, w0_leaf_369, w0_leaf_370]
#print axioms pw0_0368

theorem pw0_0370 : pw0 370 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 370 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather185]
  rw [hwe 184 (by omega), hwe 185 (by omega), hwe 186 (by omega), hwo 185 (by omega)]
  change 7*w0 (2*185) + 5*(half^1*w0 (2*184) + half^1*w0 (2*186)) - 5*w0 (2*185+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_368, w0_leaf_370, w0_leaf_371, w0_leaf_372]
#print axioms pw0_0370

theorem pw0_0372 : pw0 372 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 372 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather186]
  rw [hwe 186 (by omega), hwe 187 (by omega), hwo 186 (by omega)]
  change 7*w0 (2*186) + 5*(w0 (2*187)) - 5*w0 (2*186+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_372, w0_leaf_373, w0_leaf_374]
#print axioms pw0_0372

theorem pw0_0373 : pw0 373 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 373 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather186, gather186]
  rw [hwe 184 (by omega), hwe 186 (by omega), hwe 188 (by omega), hwo 186 (by omega), hwo 187 (by omega)]
  change -5*(w0 (2*186) - (half*w0 (2*186) + half^2*w0 (2*184) + half^2*w0 (2*188))) + 7*w0 (2*186+1) + 5*(w0 (2*187+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_368, w0_leaf_372, w0_leaf_373, w0_leaf_375, w0_leaf_376]
#print axioms pw0_0373

theorem pw0_0374 : pw0 374 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 374 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather187]
  rw [hwe 184 (by omega), hwe 186 (by omega), hwe 187 (by omega), hwe 188 (by omega), hwo 187 (by omega)]
  change 7*w0 (2*187) + 5*(half^1*w0 (2*186) + half^2*w0 (2*184) + half^2*w0 (2*188)) - 5*w0 (2*187+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_368, w0_leaf_372, w0_leaf_374, w0_leaf_375, w0_leaf_376]
#print axioms pw0_0374

end
end AspisV8R19.R780Point02WeightChunk37P0
