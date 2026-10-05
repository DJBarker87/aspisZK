import AspisV8R17.MaskWeightVector
import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.R864SemanticKernel
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
namespace AspisV8R19.R876SemanticWeightPolynomial
open AspisV8R17
open AspisV8R19.R745JointObservationPolynomial
open MvPolynomial
open scoped BigOperators
noncomputable section

universe u v

/-- CommRing mirror of the exact source-selected round block recurrence. -/
def mirrorRoundWeightBlock {R : Type u} [CommRing R] (width : Nat) (scale x : R) : List R :=
  scale * (1 - (x + x)) :: List.ofFn (fun i : Fin width => scale * (x^(i.val+2) - x))

def mirrorReverseWeightBlocks {R : Type u} [CommRing R] (width : Nat) (half : R) :
    (r : Nat) → RoundCoins R r → List R × R
  | 0, _ => ([], 1)
  | r+1, z =>
      let tail := mirrorReverseWeightBlocks width half r z.2
      (mirrorRoundWeightBlock width tail.2 z.1 ++ tail.1, tail.2 * half)

def mirrorFlatMaskWeights {R : Type u} [CommRing R] (width : Nat) (half : R)
    (r : Nat) (z : RoundCoins R r) : List R :=
  let blocks := mirrorReverseWeightBlocks width half r z
  blocks.2 :: blocks.1

def mirrorListAsFin {R : Type u} (n : Nat) (xs : List R) (h : xs.length = n) (i : Fin n) : R :=
  xs.get ⟨i.val, by omega⟩

private theorem mirrorReverse_length {R : Type u} [CommRing R] (width : Nat) (half : R)
    (r : Nat) (z : RoundCoins R r) :
    (mirrorReverseWeightBlocks width half r z).1.length = r*(width+1) := by
  induction r with
  | zero => simp [mirrorReverseWeightBlocks]
  | succ r ih =>
      cases z with
      | mk z zs =>
          simp only [mirrorReverseWeightBlocks, List.length_append,
            mirrorRoundWeightBlock, List.length_cons, List.length_ofFn]
          rw [ih]
          simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem mirrorFlat_length {R : Type u} [CommRing R] (width : Nat) (half : R)
    (r : Nat) (z : RoundCoins R r) :
    (mirrorFlatMaskWeights width half r z).length = 1 + r*(width+1) := by
  simp only [mirrorFlatMaskWeights, List.length_cons]
  rw [mirrorReverse_length]
  omega

def mirrorMaskWeights271 {R : Type u} [CommRing R] (half : R) (z : RoundCoins R 10) : Fin 271 → R :=
  mirrorListAsFin 271 (mirrorFlatMaskWeights 26 half 10 z) (by
    rw [mirrorFlat_length])

/-! These equations compare the CommRing mirror to the existing Field-only
weight implementation without using a Field structure on a polynomial ring. -/
theorem mirrorRound_eq_actual {R : Type u} [Field R] (width : Nat) (scale x : R) :
    mirrorRoundWeightBlock width scale x = roundWeightBlock width scale x := rfl

theorem mirrorReverse_eq_actual {R : Type u} [Field R] (width : Nat) (half : R)
    (r : Nat) (z : RoundCoins R r) :
    mirrorReverseWeightBlocks width half r z = reverseWeightBlocks width half r z := by
  induction r with
  | zero => rfl
  | succ r ih => cases z with
      | mk z zs =>
          simp only [mirrorReverseWeightBlocks, reverseWeightBlocks]
          rw [ih]
          rw [mirrorRound_eq_actual]

theorem mirrorFlat_eq_actual {R : Type u} [Field R] (width : Nat) (half : R)
    (r : Nat) (z : RoundCoins R r) :
    mirrorFlatMaskWeights width half r z = flatMaskWeights width half r z := by
  simp [mirrorFlatMaskWeights, flatMaskWeights, mirrorReverse_eq_actual]

theorem mirrorMaskWeights_eq_actual {R : Type u} [Field R] (half : R)
    (z : RoundCoins R 10) (i : Fin 271) :
    mirrorMaskWeights271 half z i = maskWeights271 half z i := by
  simp only [mirrorMaskWeights271, maskWeights271, mirrorFlat_eq_actual]
  congr 1

private def mapRoundCoins {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (r : Nat) → RoundCoins R r → RoundCoins S r
  | 0, _ => PUnit.unit
  | r+1, z => (f z.1, mapRoundCoins f r z.2)

theorem map_mirrorRound {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (width : Nat) (scale x : R) :
    (mirrorRoundWeightBlock width scale x).map f =
      mirrorRoundWeightBlock width (f scale) (f x) := by
  simp [mirrorRoundWeightBlock, List.map_cons, List.map_ofFn, Function.comp_def,
    map_mul, map_sub, map_add, map_one, map_pow]

theorem map_mirrorReverse {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (width : Nat) (half : R) (r : Nat) (z : RoundCoins R r) :
    ((mirrorReverseWeightBlocks width half r z).1.map f,
      f (mirrorReverseWeightBlocks width half r z).2) =
      mirrorReverseWeightBlocks width (f half) r (mapRoundCoins (R:=R) (S:=S) f r z) := by
  induction r with
  | zero => simp [mirrorReverseWeightBlocks, mapRoundCoins]
  | succ r ih =>
      cases z with
      | mk z zs =>
        have hb := ih zs
        have hl := congrArg Prod.fst hb
        have hs := congrArg Prod.snd hb
        dsimp only at hl hs
        simp only [mirrorReverseWeightBlocks, mapRoundCoins, List.map_append,
          map_mirrorRound, map_mul]
        rw [hl, hs]

theorem map_mirrorFlat {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (width : Nat) (half : R) (r : Nat) (z : RoundCoins R r) :
    (mirrorFlatMaskWeights width half r z).map f =
      mirrorFlatMaskWeights width (f half) r (mapRoundCoins (R:=R) (S:=S) f r z) := by
  have h := map_mirrorReverse f width half r z
  have hl := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp only at hl hs
  simp only [mirrorFlatMaskWeights, List.map_cons]
  rw [hl, hs]

theorem map_mirrorMaskWeights271 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (half : R)
    (z : RoundCoins R 10) (i : Fin 271) :
    f (mirrorMaskWeights271 half z i) =
      mirrorMaskWeights271 (f half) (mapRoundCoins (R:=R) (S:=S) f 10 z) i := by
  unfold mirrorMaskWeights271
  let hR : (mirrorFlatMaskWeights 26 half 10 z).length = 271 := mirrorFlat_length 26 half 10 z
  let hS : (mirrorFlatMaskWeights 26 (f half) 10 (mapRoundCoins f 10 z)).length = 271 :=
    mirrorFlat_length 26 (f half) 10 (mapRoundCoins (R:=R) (S:=S) f 10 z)
  have hmap := congrArg (fun xs => xs[i.val]?) (map_mirrorFlat f 26 half 10 z)
  simp only [List.getElem?_map, List.getElem?_eq_getElem (by rw [hR]; exact i.isLt),
    List.getElem?_eq_getElem (by rw [hS]; exact i.isLt), Option.map_some] at hmap
  exact Option.some.inj hmap

abbrev Poly := JointPoly (ZMod 2147483647)

private def polyZCoins : RoundCoins Poly 10 :=
  (pZ 0, (pZ 1, (pZ 2, (pZ 3, (pZ 4, (pZ 5, (pZ 6, (pZ 7, (pZ 8, (pZ 9, PUnit.unit))))))))))

def semanticWeightPoly (i : Fin 271) : Poly :=
  mirrorMaskWeights271 (C (1073741824 : ZMod 2147483647)) polyZCoins i

private def selectedEval : Fin 15 → ZMod 2147483647 :=
  assignment 0 0 0 0 0 R864SemanticKernel.z

private def evalHom : Poly →+* ZMod 2147483647 :=
  MvPolynomial.eval₂Hom (RingHom.id _) selectedEval

private def actualSemanticCoins : RoundCoins (ZMod 2147483647) 10 :=
  R864SemanticKernel.semanticZ

private theorem eval_pZ (j : Fin 10) : evalHom (pZ j) = R864SemanticKernel.z j := by
  simp [evalHom, pZ, selectedEval, assignment]

theorem eval_polyZCoins : mapRoundCoins evalHom 10 polyZCoins = actualSemanticCoins := by
  simp only [mapRoundCoins, polyZCoins, actualSemanticCoins, eval_pZ]
  rfl

theorem semanticWeightPoly_eval (i : Fin 271) :
    evalHom (semanticWeightPoly i) =
      maskWeights271 R864SemanticKernel.halfSelected actualSemanticCoins i := by
  rw [semanticWeightPoly, map_mirrorMaskWeights271, eval_polyZCoins]
  have hh : evalHom (C (1073741824 : ZMod 2147483647)) =
      R864SemanticKernel.halfSelected := by simp [evalHom, R864SemanticKernel.halfSelected]
  rw [hh]
  exact mirrorMaskWeights_eq_actual R864SemanticKernel.halfSelected
    actualSemanticCoins i

#print axioms mirrorRound_eq_actual
#print axioms mirrorReverse_eq_actual
#print axioms mirrorFlat_eq_actual
#print axioms mirrorMaskWeights_eq_actual
#print axioms map_mirrorRound
#print axioms map_mirrorReverse
#print axioms map_mirrorFlat
#print axioms map_mirrorMaskWeights271
#print axioms eval_polyZCoins
#print axioms semanticWeightPoly_eval
end
end AspisV8R19.R876SemanticWeightPolynomial
