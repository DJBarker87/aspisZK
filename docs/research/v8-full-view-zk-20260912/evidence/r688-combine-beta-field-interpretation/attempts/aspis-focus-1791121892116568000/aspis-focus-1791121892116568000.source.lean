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

def c2Vec (a2 : Std.Array U32 48#usize) (group : Fin 3) (slot : U4) : QM31Exact :=
  decode4 (fun limb =>
    arrayAt a2 ⟨16 * group.val + 4 * slot.val + limb.val, by omega⟩)

def mixedMatrix (powers : query_arithmetic.BetaCoefficients) (group : Fin 3) :
    Std.Array (Std.Array U32 4#usize) 4#usize :=
  Std.Array.make 4#usize [
    arrayAt powers.mixed ⟨4 * group.val, by omega⟩,
    arrayAt powers.mixed ⟨4 * group.val + 1, by omega⟩,
    arrayAt powers.mixed ⟨4 * group.val + 2, by omega⟩,
    arrayAt powers.mixed ⟨4 * group.val + 3, by omega⟩]

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
      (base (arrayAt a2 ⟨16*group.val+4*slot.val, by omega⟩))
      (base (arrayAt a2 ⟨16*group.val+4*slot.val+1, by omega⟩))
      (base (arrayAt a2 ⟨16*group.val+4*slot.val+2, by omega⟩))
      (base (arrayAt a2 ⟨16*group.val+4*slot.val+3, by omega⟩))

-- R687 gives the source result and canonical 38-term representatives. The
-- field-coordinate normalization and 12 = 3×4 regrouping are proved below.
#print base
#print decode4
#print coeffVec
#print mixedMatrix
#print interpreted
end
end AspisV8R19.R688CombineBetaFieldInterpretation
