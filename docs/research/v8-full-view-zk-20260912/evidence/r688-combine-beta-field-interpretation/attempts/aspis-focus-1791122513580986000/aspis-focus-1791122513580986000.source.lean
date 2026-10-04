import AspisV8R19.R687CombineBetaComposition
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R688CombineBetaFieldInterpretation
open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact P)
open AspisV8R19.R646CombineLoopExecution
open AspisV8R19.R687CombineBetaComposition
open scoped BigOperators
noncomputable section

private abbrev U4 := Fin 4

def base (x : U32) : M31Exact := (x.val : M31Exact)

def decode4 (x : U4 → U32) : QM31Exact :=
  ⟨⟨base (x 0), base (x 1)⟩, ⟨base (x 2), base (x 3)⟩⟩

def outputField (lane : U4 → U4 → U32) (slot : U4) : QM31Exact :=
  decode4 (lane slot)

def coeffVec (powers : query_arithmetic.BetaCoefficients) (i : Fin 26) : QM31Exact :=
  decode4 (fun limb => arrayAt (arrayAt powers.c1_limbs i) limb)

def c1Scalar (a1 : Std.Array U32 104#usize) (slot : U4) (i : Fin 26) : M31Exact :=
  base (arrayAt (c1Chunk a1 slot) i)

def c2Index (group : Fin 3) (slot limb : U4) : Fin (48#usize : Usize).val :=
  ⟨16 * group.val + 4 * slot.val + limb.val, by
    have h48 : (48#usize : Usize).val = 48 := by scalar_tac
    omega⟩

def mixedIndex (group : Fin 3) (row : Fin 4) : Fin (12#usize : Usize).val :=
  ⟨4 * group.val + row.val, by
    have h12 : (12#usize : Usize).val = 12 := by scalar_tac
    omega⟩

def c2Vec (a2 : Std.Array U32 48#usize) (group : Fin 3) (slot : U4) : QM31Exact :=
  decode4 (fun limb =>
    arrayAt a2 (c2Index group slot limb))

def mixedMatrix (powers : query_arithmetic.BetaCoefficients) (group : Fin 3) :
    Std.Array (Std.Array U32 4#usize) 4#usize :=
  Std.Array.make 4#usize [
    arrayAt powers.mixed (mixedIndex group 0),
    arrayAt powers.mixed (mixedIndex group 1),
    arrayAt powers.mixed (mixedIndex group 2),
    arrayAt powers.mixed (mixedIndex group 3)]

/-- The same coordinate action used by R620, written here over the R614
generated array types to avoid combining incompatible generated type modules. -/
def matrixCoordinate (m : Std.Array (Std.Array U32 4#usize) 4#usize)
    (e f g h : M31Exact) (k : Fin 4) : M31Exact :=
  e * base (arrayAt (arrayAt m ⟨0, by decide⟩) k) +
  f * base (arrayAt (arrayAt m ⟨1, by decide⟩) k) +
  g * base (arrayAt (arrayAt m ⟨2, by decide⟩) k) +
  h * base (arrayAt (arrayAt m ⟨3, by decide⟩) k)

def matrixAction (m : Std.Array (Std.Array U32 4#usize) 4#usize)
    (e f g h : M31Exact) : QM31Exact :=
  ⟨⟨matrixCoordinate m e f g h ⟨0, by decide⟩,
      matrixCoordinate m e f g h ⟨1, by decide⟩⟩,
    ⟨matrixCoordinate m e f g h ⟨2, by decide⟩,
      matrixCoordinate m e f g h ⟨3, by decide⟩⟩⟩

def rawCoordinate (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (powers : query_arithmetic.BetaCoefficients) (slot limb : U4) : M31Exact :=
  (∑ i : Fin 26,
      base (arrayAt (c1Chunk a1 slot) i) *
        base (arrayAt (arrayAt powers.c1_limbs i) limb)) +
  ∑ j : Fin 12,
    base (arrayAt a2 ⟨16 * (j.val / 4) + 4 * (sourceIndex slot).val + j.val % 4,
      AspisV8R19.R616MixedLimbExecution.mixedC2Index_lt48 j (sourceIndex slot)
        (by
          unfold sourceIndex
          change slot.val < 4
          exact slot.isLt)⟩) *
      base (arrayAt (arrayAt powers.mixed j) limb)

lemma base_of_mixed38 (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (powers : query_arithmetic.BetaCoefficients) (slot limb : U4) (x : U32)
    (hx : x.val = mixed38 a1 a2 powers slot limb) :
    base x = rawCoordinate a1 a2 powers slot limb := by
  rw [base, hx, mixed38, ZMod.natCast_mod]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  rfl

lemma sum_fin12_group (f : Fin 12 → M31Exact) :
    (∑ j : Fin 12, f j) = ∑ group : Fin 3, ∑ row : Fin 4,
      f ⟨4 * group.val + row.val, by omega⟩ := by
  refine (Equiv.sum_comp (finProdFinEquiv (m := 3) (n := 4)) f).symm.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv] <;> omega

def interpreted (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (powers : query_arithmetic.BetaCoefficients) (slot : U4) : QM31Exact :=
  (∑ i : Fin 26, c1Scalar a1 slot i • coeffVec powers i) +
  ∑ group : Fin 3,
    matrixAction (mixedMatrix powers group)
      (base (arrayAt a2 (c2Index group slot 0)))
      (base (arrayAt a2 (c2Index group slot 1)))
      (base (arrayAt a2 (c2Index group slot 2)))
      (base (arrayAt a2 (c2Index group slot 3)))

def coordinate (x : QM31Exact) (limb : U4) : M31Exact :=
  match limb with
  | ⟨0, _⟩ => x.re.re
  | ⟨1, _⟩ => x.re.im
  | ⟨2, _⟩ => x.im.re
  | ⟨3, _⟩ => x.im.im

def reReHom : QM31Exact →+ M31Exact where
  toFun x := x.re.re
  map_zero' := rfl
  map_add' _ _ := rfl

def reImHom : QM31Exact →+ M31Exact where
  toFun x := x.re.im
  map_zero' := rfl
  map_add' _ _ := rfl

def imReHom : QM31Exact →+ M31Exact where
  toFun x := x.im.re
  map_zero' := rfl
  map_add' _ _ := rfl

def imImHom : QM31Exact →+ M31Exact where
  toFun x := x.im.im
  map_zero' := rfl
  map_add' _ _ := rfl

lemma sum_re_re {ι : Type} [Fintype ι] (f : ι → QM31Exact) :
    (∑ i, f i).re.re = ∑ i, (f i).re.re := by
  exact map_sum reReHom f Finset.univ

lemma sum_re_im {ι : Type} [Fintype ι] (f : ι → QM31Exact) :
    (∑ i, f i).re.im = ∑ i, (f i).re.im := by
  exact map_sum reImHom f Finset.univ

lemma sum_im_re {ι : Type} [Fintype ι] (f : ι → QM31Exact) :
    (∑ i, f i).im.re = ∑ i, (f i).im.re := by
  exact map_sum imReHom f Finset.univ

lemma sum_im_im {ι : Type} [Fintype ι] (f : ι → QM31Exact) :
    (∑ i, f i).im.im = ∑ i, (f i).im.im := by
  exact map_sum imImHom f Finset.univ

lemma interpreted_coordinate (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (powers : query_arithmetic.BetaCoefficients) (slot limb : U4) :
    coordinate (interpreted a1 a2 powers slot) limb =
      (∑ i : Fin 26,
        base (arrayAt (c1Chunk a1 slot) i) *
          base (arrayAt (arrayAt powers.c1_limbs i) limb)) +
      ∑ group : Fin 3,
        matrixCoordinate (mixedMatrix powers group)
          (base (arrayAt a2 (c2Index group slot 0)))
          (base (arrayAt a2 (c2Index group slot 1)))
          (base (arrayAt a2 (c2Index group slot 2)))
          (base (arrayAt a2 (c2Index group slot 3))) limb := by
  fin_cases limb
  · simp only [coordinate, interpreted, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    rw [sum_re_re, sum_re_re]
    simp [c1Scalar, coeffVec, decode4, matrixAction]
  · simp only [coordinate, interpreted, QuadraticAlgebra.re_add]
    rw [QuadraticAlgebra.im_add]
    rw [sum_re_im, sum_re_im]
    simp [c1Scalar, coeffVec, decode4, matrixAction]
  · simp only [coordinate, interpreted, QuadraticAlgebra.im_add, QuadraticAlgebra.re_add]
    rw [sum_im_re, sum_im_re]
    simp [c1Scalar, coeffVec, decode4, matrixAction]
  · simp only [coordinate, interpreted, QuadraticAlgebra.im_add, QuadraticAlgebra.re_add]
    rw [sum_im_im, sum_im_im]
    simp [c1Scalar, coeffVec, decode4, matrixAction]

theorem combine_beta_field_interpretation
    (c1 c2 : Slice U8) (powers : query_arithmetic.BetaCoefficients)
    (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (h1 : query_arithmetic.r55_decode_into c1 (Array.repeat 104#usize 0#u32) =
      .ok (core.result.Result.Ok (), a1))
    (h2 : query_arithmetic.r55_decode_into c2 (Array.repeat 48#usize 0#u32) =
      .ok (core.result.Result.Ok (), a2))
    (hp1 : ∀ i : Fin 26, ∀ r : Fin 4, (arrayAt (arrayAt powers.c1_limbs i) r).val < 2147483647)
    (hp2 : ∀ i : Fin 12, ∀ r : Fin 4, (arrayAt (arrayAt powers.mixed i) r).val < 2147483647) :
    ∃ lane : U4 → U4 → U32,
      query_arithmetic.combine_beta c1 c2 powers = .ok (core.result.Result.Ok (laneArray lane)) ∧
      (∀ slot limb, (lane slot limb).val < 2147483647) ∧
      ∀ slot, outputField lane slot = interpreted a1 a2 powers slot := by
  obtain ⟨lane, hcombine, hlanes⟩ :=
    combine_beta_success_canonical_limbs c1 c2 powers a1 a2 h1 h2 hp1 hp2
  refine ⟨lane, hcombine, ?_, ?_⟩
  · intro slot limb
    exact (hlanes slot limb).1
  · intro slot
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext
    case re.re =>
      change base (lane slot 0) = coordinate (interpreted a1 a2 powers slot) 0
      exact (base_of_mixed38 a1 a2 powers slot 0 (lane slot 0) (hlanes slot 0).2).trans
        (interpreted_coordinate a1 a2 powers slot 0).symm
    case re.im =>
      change base (lane slot 1) = coordinate (interpreted a1 a2 powers slot) 1
      exact (base_of_mixed38 a1 a2 powers slot 1 (lane slot 1) (hlanes slot 1).2).trans
        (interpreted_coordinate a1 a2 powers slot 1).symm
    case im.re =>
      change base (lane slot 2) = coordinate (interpreted a1 a2 powers slot) 2
      exact (base_of_mixed38 a1 a2 powers slot 2 (lane slot 2) (hlanes slot 2).2).trans
        (interpreted_coordinate a1 a2 powers slot 2).symm
    case im.im =>
      change base (lane slot 3) = coordinate (interpreted a1 a2 powers slot) 3
      exact (base_of_mixed38 a1 a2 powers slot 3 (lane slot 3) (hlanes slot 3).2).trans
        (interpreted_coordinate a1 a2 powers slot 3).symm
#print axioms combine_beta_field_interpretation
end
end AspisV8R19.R688CombineBetaFieldInterpretation
