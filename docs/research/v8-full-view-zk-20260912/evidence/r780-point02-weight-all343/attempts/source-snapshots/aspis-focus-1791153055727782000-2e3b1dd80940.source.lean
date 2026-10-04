import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk01
import AspisV8R19.R780Point02WeightSharedChunk02
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

namespace AspisV8R19.R780Point02WeightChunk12P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk01
open AspisV8R19.R780Point02WeightSharedChunk02
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

theorem pw0_0158 : pw0 158 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 158 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather79]
  rw [hwe 64 (by omega), hwe 72 (by omega), hwe 76 (by omega), hwe 78 (by omega), hwe 79 (by omega), hwe 80 (by omega), hwo 79 (by omega)]
  change 7*w0 (2*79) + 5*(half^1*w0 (2*78) + half^2*w0 (2*76) + half^3*w0 (2*72) + half^4*w0 (2*64) + half^4*w0 (2*80)) - 5*w0 (2*79+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) - 5*(0)
  rw [w0_leaf_128, w0_leaf_144, w0_leaf_152, w0_leaf_156, w0_leaf_158, w0_leaf_159, w0_leaf_160]
#print axioms pw0_0158

theorem pw0_0160 : pw0 160 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 160 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather80]
  rw [hwe 80 (by omega), hwe 81 (by omega), hwo 80 (by omega)]
  change 7*w0 (2*80) + 5*(w0 (2*81)) - 5*w0 (2*80+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_160, w0_leaf_161, w0_leaf_162]
#print axioms pw0_0160

theorem pw0_0161 : pw0 161 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 161 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather80, gather80]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwo 80 (by omega), hwo 81 (by omega)]
  change -5*(w0 (2*80) - (half*w0 (2*80) + half*w0 (2*82))) + 7*w0 (2*80+1) + 5*(w0 (2*81+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_160, w0_leaf_161, w0_leaf_163, w0_leaf_164]
#print axioms pw0_0161

theorem pw0_0162 : pw0 162 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 162 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather81]
  rw [hwe 80 (by omega), hwe 81 (by omega), hwe 82 (by omega), hwo 81 (by omega)]
  change 7*w0 (2*81) + 5*(half^1*w0 (2*80) + half^1*w0 (2*82)) - 5*w0 (2*81+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_160, w0_leaf_162, w0_leaf_163, w0_leaf_164]
#print axioms pw0_0162

end
end AspisV8R19.R780Point02WeightChunk12P0
