import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk07
import AspisV8R19.R780Point02WeightSharedChunk08
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

namespace AspisV8R19.R780Point02WeightChunk34P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk07
open AspisV8R19.R780Point02WeightSharedChunk08
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

theorem pw2_0331 : pw2 331 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 331 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather165, gather165]
  rw [hwe 165 (by omega), hwe 167 (by omega), hwo 164 (by omega), hwo 165 (by omega), hwo 166 (by omega)]
  change -5*(w2 (2*165) - (half*w2 (2*165) + half*w2 (2*167))) + 7*w2 (2*165+1) + 5*(half^1*w2 (2*164+1) + half^1*w2 (2*166+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_329, w2_leaf_330, w2_leaf_331, w2_leaf_333, w2_leaf_334]
#print axioms pw2_0331

theorem pw2_0332 : pw2 332 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 332 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather166]
  rw [hwe 166 (by omega), hwe 167 (by omega), hwo 166 (by omega)]
  change 7*w2 (2*166) + 5*(w2 (2*167)) - 5*w2 (2*166+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_332, w2_leaf_333, w2_leaf_334]
#print axioms pw2_0332

theorem pw2_0333 : pw2 333 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 333 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather166, gather166]
  rw [hwe 160 (by omega), hwe 164 (by omega), hwe 166 (by omega), hwe 168 (by omega), hwo 166 (by omega), hwo 167 (by omega)]
  change -5*(w2 (2*166) - (half*w2 (2*166) + half^2*w2 (2*164) + half^3*w2 (2*160) + half^3*w2 (2*168))) + 7*w2 (2*166+1) + 5*(w2 (2*167+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_320, w2_leaf_328, w2_leaf_332, w2_leaf_333, w2_leaf_335, w2_leaf_336]
#print axioms pw2_0333

theorem pw2_0335 : pw2 335 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 335 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather167, gather167]
  rw [hwe 161 (by omega), hwe 165 (by omega), hwe 167 (by omega), hwe 169 (by omega), hwo 160 (by omega), hwo 164 (by omega), hwo 166 (by omega), hwo 167 (by omega), hwo 168 (by omega)]
  change -5*(w2 (2*167) - (half*w2 (2*167) + half^2*w2 (2*165) + half^3*w2 (2*161) + half^3*w2 (2*169))) + 7*w2 (2*167+1) + 5*(half^1*w2 (2*166+1) + half^2*w2 (2*164+1) + half^3*w2 (2*160+1) + half^3*w2 (2*168+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0))
  rw [w2_leaf_321, w2_leaf_322, w2_leaf_329, w2_leaf_330, w2_leaf_333, w2_leaf_334, w2_leaf_335, w2_leaf_337, w2_leaf_338]
#print axioms pw2_0335

theorem pw2_0336 : pw2 336 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 336 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather168]
  rw [hwe 168 (by omega), hwe 169 (by omega), hwo 168 (by omega)]
  change 7*w2 (2*168) + 5*(w2 (2*169)) - 5*w2 (2*168+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_336, w2_leaf_337, w2_leaf_338]
#print axioms pw2_0336

theorem pw2_0337 : pw2 337 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 337 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather168, gather168]
  rw [hwe 168 (by omega), hwe 170 (by omega), hwo 168 (by omega), hwo 169 (by omega)]
  change -5*(w2 (2*168) - (half*w2 (2*168) + half*w2 (2*170))) + 7*w2 (2*168+1) + 5*(w2 (2*169+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_336, w2_leaf_337, w2_leaf_339, w2_leaf_340]
#print axioms pw2_0337

theorem pw2_0339 : pw2 339 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 339 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather169, gather169]
  rw [hwe 169 (by omega), hwe 171 (by omega), hwo 168 (by omega), hwo 169 (by omega), hwo 170 (by omega)]
  change -5*(w2 (2*169) - (half*w2 (2*169) + half*w2 (2*171))) + 7*w2 (2*169+1) + 5*(half^1*w2 (2*168+1) + half^1*w2 (2*170+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_337, w2_leaf_338, w2_leaf_339, w2_leaf_341, w2_leaf_342]
#print axioms pw2_0339

theorem pw2_0340 : pw2 340 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 340 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather170]
  rw [hwe 170 (by omega), hwe 171 (by omega), hwo 170 (by omega)]
  change 7*w2 (2*170) + 5*(w2 (2*171)) - 5*w2 (2*170+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_340, w2_leaf_341, w2_leaf_342]
#print axioms pw2_0340

end
end AspisV8R19.R780Point02WeightChunk34P2
