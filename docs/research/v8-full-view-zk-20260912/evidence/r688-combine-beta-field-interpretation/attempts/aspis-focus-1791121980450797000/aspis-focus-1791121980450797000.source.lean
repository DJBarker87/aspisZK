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

def interpreted (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (powers : query_arithmetic.BetaCoefficients) (slot : U4) : QM31Exact :=
  (∑ i : Fin 26, c1Scalar a1 slot i • coeffVec powers i) +
  ∑ group : Fin 3,
    matrixAction (mixedMatrix powers group)
      (base (arrayAt a2 (c2Index group slot 0)))
      (base (arrayAt a2 (c2Index group slot 1)))
      (base (arrayAt a2 (c2Index group slot 2)))
      (base (arrayAt a2 (c2Index group slot 3)))

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
    all_goals
      simp only [outputField, decode4]
      trace_state
      sorry
end
end AspisV8R19.R688CombineBetaFieldInterpretation
