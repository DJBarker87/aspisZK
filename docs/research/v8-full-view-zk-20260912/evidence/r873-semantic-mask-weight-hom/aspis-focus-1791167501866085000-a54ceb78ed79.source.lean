import AspisV8R17.MaskWeightVector
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R873SemanticMaskWeightHom
open AspisV8R17
noncomputable section
variable {F K : Type*} [Field F] [Field K]

def mapCoins (f : F →+* K) : (r : Nat) → RoundCoins F r → RoundCoins K r
  | 0, _ => PUnit.unit
  | r+1, z => (f z.1, mapCoins f r z.2)

theorem map_roundWeightBlock (f : F →+* K) (width : Nat) (scale x : F) :
    (roundWeightBlock width scale x).map f = roundWeightBlock width (f scale) (f x) := by
  simp only [roundWeightBlock, List.map_cons, List.map_ofFn, Function.comp_def,
    map_mul, map_sub, map_add, map_one, map_pow]

theorem map_reverseWeightBlocks (f : F →+* K) (width : Nat) (half : F)
    (r : Nat) (z : RoundCoins F r) :
    ((reverseWeightBlocks width half r z).1.map f, f (reverseWeightBlocks width half r z).2) =
      reverseWeightBlocks width (f half) r (mapCoins f r z) := by
  induction r with
  | zero => simp [reverseWeightBlocks, mapCoins]
  | succ r ih =>
    have hb := ih z.2
    have hl := congrArg Prod.fst hb
    have hs := congrArg Prod.snd hb
    dsimp only at hl hs
    simp only [reverseWeightBlocks, mapCoins, List.map_append, map_roundWeightBlock, map_mul]
    rw [hl, hs]

theorem map_flatMaskWeights (f : F →+* K) (width : Nat) (half : F)
    (r : Nat) (z : RoundCoins F r) :
    (flatMaskWeights width half r z).map f = flatMaskWeights width (f half) r (mapCoins f r z) := by
  have h := map_reverseWeightBlocks f width half r z
  have hl := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp only at hl hs
  simp only [flatMaskWeights, List.map_cons]
  rw [hl, hs]

theorem map_maskWeights271 (f : F →+* K) (half : F) (z : RoundCoins F 10) (i : Fin 271) :
    f (maskWeights271 half z i) = maskWeights271 (f half) (mapCoins f 10 z) i := by
  have h := congrArg (fun xs => xs[i.val]?) (map_flatMaskWeights f 26 half 10 z)
  have hlen := flatMaskWeights_length 26 half 10 z
  have hlenK := flatMaskWeights_length 26 (f half) 10 (mapCoins f 10 z)
  have hi : i.val < (flatMaskWeights 26 half 10 z).length := by rw [hlen]; omega
  have hiK : i.val < (flatMaskWeights 26 (f half) 10 (mapCoins f 10 z)).length := by rw [hlenK]; omega
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiK,
    Option.map_some] at h
  exact Option.some.inj h

#print axioms map_roundWeightBlock
#print axioms map_reverseWeightBlocks
#print axioms map_flatMaskWeights
#print axioms map_maskWeights271
end
end AspisV8R19.R873SemanticMaskWeightHom
