import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk00
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R780Point02WeightSharedChunk09
import AspisV8R19.R780Point02WeightSharedChunk10
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

namespace AspisV8R19.R780Point02WeightChunk40P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk00
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R19.R780Point02WeightSharedChunk09
open AspisV8R19.R780Point02WeightSharedChunk10
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

theorem pw2_0511 : pw2 511 = -5*((([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0))) + 7*(([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 511 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather255, gather255]
  rw [hwe 1 (by omega), hwe 129 (by omega), hwe 193 (by omega), hwe 225 (by omega), hwe 241 (by omega), hwe 249 (by omega), hwe 253 (by omega), hwe 255 (by omega), hwe 257 (by omega), hwo 0 (by omega), hwo 128 (by omega), hwo 192 (by omega), hwo 224 (by omega), hwo 240 (by omega), hwo 248 (by omega), hwo 252 (by omega), hwo 254 (by omega), hwo 255 (by omega), hwo 256 (by omega)]
  change -5*(w2 (2*255) - (half*w2 (2*255) + half^2*w2 (2*253) + half^3*w2 (2*249) + half^4*w2 (2*241) + half^5*w2 (2*225) + half^6*w2 (2*193) + half^7*w2 (2*129) + half^8*w2 (2*1) + half^8*w2 (2*257))) + 7*w2 (2*255+1) + 5*(half^1*w2 (2*254+1) + half^2*w2 (2*252+1) + half^3*w2 (2*248+1) + half^4*w2 (2*240+1) + half^5*w2 (2*224+1) + half^6*w2 (2*192+1) + half^7*w2 (2*128+1) + half^8*w2 (2*0+1) + half^8*w2 (2*256+1)) = -5*((([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0))) + 7*(([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0))
  rw [w2_leaf_1, w2_leaf_2, w2_leaf_257, w2_leaf_258, w2_leaf_385, w2_leaf_386, w2_leaf_449, w2_leaf_450, w2_leaf_481, w2_leaf_482, w2_leaf_497, w2_leaf_498, w2_leaf_505, w2_leaf_506, w2_leaf_509, w2_leaf_510, w2_leaf_511, w2_leaf_513, w2_leaf_514]
#print axioms pw2_0511

theorem pw2_0624 : pw2 624 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 624 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather312]
  rw [hwe 312 (by omega), hwe 313 (by omega), hwo 312 (by omega)]
  change 7*w2 (2*312) + 5*(w2 (2*313)) - 5*w2 (2*312+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_624, w2_leaf_625, w2_leaf_626]
#print axioms pw2_0624

theorem pw2_0626 : pw2 626 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 626 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather313]
  rw [hwe 312 (by omega), hwe 313 (by omega), hwe 314 (by omega), hwo 313 (by omega)]
  change 7*w2 (2*313) + 5*(half^1*w2 (2*312) + half^1*w2 (2*314)) - 5*w2 (2*313+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_624, w2_leaf_626, w2_leaf_627, w2_leaf_628]
#print axioms pw2_0626

theorem pw2_0628 : pw2 628 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 628 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather314]
  rw [hwe 314 (by omega), hwe 315 (by omega), hwo 314 (by omega)]
  change 7*w2 (2*314) + 5*(w2 (2*315)) - 5*w2 (2*314+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_628, w2_leaf_629, w2_leaf_630]
#print axioms pw2_0628

theorem pw2_0629 : pw2 629 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 629 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather314, gather314]
  rw [hwe 312 (by omega), hwe 314 (by omega), hwe 316 (by omega), hwo 314 (by omega), hwo 315 (by omega)]
  change -5*(w2 (2*314) - (half*w2 (2*314) + half^2*w2 (2*312) + half^2*w2 (2*316))) + 7*w2 (2*314+1) + 5*(w2 (2*315+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_624, w2_leaf_628, w2_leaf_629, w2_leaf_631, w2_leaf_632]
#print axioms pw2_0629

theorem pw2_0630 : pw2 630 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 630 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather315]
  rw [hwe 312 (by omega), hwe 314 (by omega), hwe 315 (by omega), hwe 316 (by omega), hwo 315 (by omega)]
  change 7*w2 (2*315) + 5*(half^1*w2 (2*314) + half^2*w2 (2*312) + half^2*w2 (2*316)) - 5*w2 (2*315+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w2_leaf_624, w2_leaf_628, w2_leaf_630, w2_leaf_631, w2_leaf_632]
#print axioms pw2_0630

theorem pw2_0632 : pw2 632 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 632 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather316]
  rw [hwe 316 (by omega), hwe 317 (by omega), hwo 316 (by omega)]
  change 7*w2 (2*316) + 5*(w2 (2*317)) - 5*w2 (2*316+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_632, w2_leaf_633, w2_leaf_634]
#print axioms pw2_0632

theorem pw2_0633 : pw2 633 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 633 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather316, gather316]
  rw [hwe 316 (by omega), hwe 318 (by omega), hwo 316 (by omega), hwo 317 (by omega)]
  change -5*(w2 (2*316) - (half*w2 (2*316) + half*w2 (2*318))) + 7*w2 (2*316+1) + 5*(w2 (2*317+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_632, w2_leaf_633, w2_leaf_635, w2_leaf_636]
#print axioms pw2_0633

end
end AspisV8R19.R780Point02WeightChunk40P2
