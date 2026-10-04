import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk01
import AspisV8R19.R780Point02WeightSharedChunk02
import AspisV8R19.R780Point02WeightSharedChunk03
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

namespace AspisV8R19.R780Point02WeightChunk17P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk01
open AspisV8R19.R780Point02WeightSharedChunk02
open AspisV8R19.R780Point02WeightSharedChunk03
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

theorem pw0_0188 : pw0 188 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 188 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather94]
  rw [hwe 94 (by omega), hwe 95 (by omega), hwo 94 (by omega)]
  change 7*w0 (2*94) + 5*(w0 (2*95)) - 5*w0 (2*94+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_188, w0_leaf_189, w0_leaf_190]
#print axioms pw0_0188

theorem pw0_0190 : pw0 190 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 190 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather95]
  rw [hwe 64 (by omega), hwe 80 (by omega), hwe 88 (by omega), hwe 92 (by omega), hwe 94 (by omega), hwe 95 (by omega), hwe 96 (by omega), hwo 95 (by omega)]
  change 7*w0 (2*95) + 5*(half^1*w0 (2*94) + half^2*w0 (2*92) + half^3*w0 (2*88) + half^4*w0 (2*80) + half^5*w0 (2*64) + half^5*w0 (2*96)) - 5*w0 (2*95+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) - 5*(0)
  rw [w0_leaf_128, w0_leaf_160, w0_leaf_176, w0_leaf_184, w0_leaf_188, w0_leaf_190, w0_leaf_191, w0_leaf_192]
#print axioms pw0_0190

theorem pw0_0191 : pw0 191 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 191 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather95, gather95]
  rw [hwe 65 (by omega), hwe 81 (by omega), hwe 89 (by omega), hwe 93 (by omega), hwe 95 (by omega), hwe 97 (by omega), hwo 64 (by omega), hwo 80 (by omega), hwo 88 (by omega), hwo 92 (by omega), hwo 94 (by omega), hwo 95 (by omega), hwo 96 (by omega)]
  change -5*(w0 (2*95) - (half*w0 (2*95) + half^2*w0 (2*93) + half^3*w0 (2*89) + half^4*w0 (2*81) + half^5*w0 (2*65) + half^5*w0 (2*97))) + 7*w0 (2*95+1) + 5*(half^1*w0 (2*94+1) + half^2*w0 (2*92+1) + half^3*w0 (2*88+1) + half^4*w0 (2*80+1) + half^5*w0 (2*64+1) + half^5*w0 (2*96+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))
  rw [w0_leaf_129, w0_leaf_130, w0_leaf_161, w0_leaf_162, w0_leaf_177, w0_leaf_178, w0_leaf_185, w0_leaf_186, w0_leaf_189, w0_leaf_190, w0_leaf_191, w0_leaf_193, w0_leaf_194]
#print axioms pw0_0191

theorem pw0_0192 : pw0 192 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 192 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather96]
  rw [hwe 96 (by omega), hwe 97 (by omega), hwo 96 (by omega)]
  change 7*w0 (2*96) + 5*(w0 (2*97)) - 5*w0 (2*96+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_192, w0_leaf_193, w0_leaf_194]
#print axioms pw0_0192

end
end AspisV8R19.R780Point02WeightChunk17P0
