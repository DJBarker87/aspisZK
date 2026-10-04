import AspisV8R19.SparseGCoreInverse
import AspisV8R17.WeightedScatter
import AspisV8R17.SourceScatter
import AspisV8R19.SparseGPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
namespace AspisV8R19.R574SparseGCorePolynomial

open AspisR19.SparseGCoreInverse AspisV8R17 AspisR19.SparseGPolynomial

variable {F : Type*} [Field F] [NeZero (2 : F)]

def ch (s : Nat) (x : Fin 271 → F) (r : Nat) : F :=
  if r % 4 = 0 then channel (extend x) (r / 4) s else 0

def nz (x : Fin 271 → F) (r : Nat) : F :=
  if r % 4 = 0 then 0 else channel (extend x) (r / 4) (r % 4)

def weightedQ (alpha : F) (x : Fin 271 → F) (r : Nat) : F :=
  nz x r - alpha * ch 1 x r - alpha ^ 2 * ch 2 x r - alpha ^ 3 * ch 3 x r

omit [NeZero (2 : F)] in
theorem weightedQ_one (x : Fin 271 → F) (r : Nat) :
    weightedQ 1 x r = quotient (extend x) r := by
  by_cases hr : r % 4 = 0
  · simp [weightedQ, nz, ch, quotient, hr]
    ring
  · simp [weightedQ, nz, ch, quotient, hr]

def coreMap (half alpha a b c : F) (x : Fin 271 → F) (i : Fin 271) : F :=
  sourceChord half (weightedQ alpha x) a b c (128 + 3 * i.val)

theorem coreMap_witness (half : F) (x : Fin 271 → F) (i : Fin 271) :
    coreMap half 1 2 0 0 x i = (2 : F) * finiteBlock x i := by
  rw [coreMap]
  have hq : weightedQ 1 x = quotient (extend x) := by
    funext r
    exact weightedQ_one x r
  rw [hq]
  have hi : 128 + 3 * i.val < 1024 := by omega
  rw [AspisR19.SparseGPolynomial.source_scalar half 2 (quotient (extend x))
    (128 + 3 * i.val) hi]
  rw [source_block]
  rfl

theorem sourceChord_components (half : F) (q : Nat → F) (a b c : F) (r : Nat) :
    sourceChord half q a b c r =
      a * sourceChord half q 1 0 0 r +
      b * sourceChord half q 0 1 0 r +
      c * sourceChord half q 0 0 1 r := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  exact chordCoefficient_components _ _ q a b c r

theorem sourceChord_linear (half : F) (q s : Nat → F) (u v a b c : F) (r : Nat) :
    sourceChord half (fun i => u * q i + v * s i) a b c r =
      u * sourceChord half q a b c r + v * sourceChord half s a b c r := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [zeroExtend_linear 1024 q s u v]
  exact chordCoefficient_linear _ _ _ _ a b c u v r

theorem extend_add (x y : Fin 271 → F) :
    extend (x + y) = fun r => extend x r + extend y r := by
  funext r
  unfold extend
  split_ifs <;> simp

theorem extend_smul (t : F) (x : Fin 271 → F) :
    extend (t • x) = fun r => t * extend x r := by
  funext r
  unfold extend
  split_ifs <;> simp

theorem channel_add (q s : Nat → F) (d k : Nat) :
    channel (q + s) d k = channel q d k + channel s d k := by
  unfold channel
  split_ifs <;> simp <;> ring

theorem channel_smul (t : F) (q : Nat → F) (d k : Nat) :
    channel (fun r => t * q r) d k = t * channel q d k := by
  unfold channel
  split_ifs <;> simp <;> ring

theorem ch_add (n : Nat) (x y : Fin 271 → F) :
    ch n (x + y) = fun r => ch n x r + ch n y r := by
  funext r
  unfold ch
  split_ifs with h
  · rw [← channel_add, extend_add]
  · simp

theorem ch_smul (n : Nat) (t : F) (x : Fin 271 → F) :
    ch n (t • x) = fun r => t * ch n x r := by
  funext r
  unfold ch
  split_ifs with h
  · rw [channel_smul, extend_smul]
  · simp

theorem nz_add (x y : Fin 271 → F) :
    nz (x + y) = fun r => nz x r + nz y r := by
  funext r
  unfold nz
  split_ifs with h
  · simp
  · rw [← channel_add, extend_add]

theorem nz_smul (t : F) (x : Fin 271 → F) :
    nz (t • x) = fun r => t * nz x r := by
  funext r
  unfold nz
  split_ifs with h
  · simp
  · rw [channel_smul, extend_smul]

theorem weightedQ_add (alpha : F) (x y : Fin 271 → F) :
    weightedQ alpha (x + y) = fun r => weightedQ alpha x r + weightedQ alpha y r := by
  funext r
  simp only [weightedQ, nz_add, ch_add]
  ring

theorem weightedQ_smul (alpha t : F) (x : Fin 271 → F) :
    weightedQ alpha (t • x) = fun r => t * weightedQ alpha x r := by
  funext r
  simp only [weightedQ, nz_smul, ch_smul]
  ring

theorem coreMap_add (half alpha a b c : F) (x y : Fin 271 → F) (i : Fin 271) :
    coreMap half alpha a b c (x + y) i =
      coreMap half alpha a b c x i + coreMap half alpha a b c y i := by
  unfold coreMap
  rw [weightedQ_add, sourceChord_linear half (weightedQ alpha x) (weightedQ alpha y)
    1 1 a b c (128+3*i.val)]
  ring

theorem coreMap_smul (half alpha a b c t : F) (x : Fin 271 → F) (i : Fin 271) :
    coreMap half alpha a b c (t • x) i = t * coreMap half alpha a b c x i := by
  unfold coreMap
  rw [weightedQ_smul, sourceChord_linear half (weightedQ alpha x) 0 t 0 a b c
    (128+3*i.val)]
  simp

def coreLinearMap (half alpha a b c : F) : (Fin 271 → F) →ₗ[F] (Fin 271 → F) where
  toFun x i := coreMap half alpha a b c x i
  map_add' x y := by
    funext i
    exact coreMap_add half alpha a b c x y i
  map_smul' t x := by
    funext i
    exact coreMap_smul half alpha a b c t x i

def basis (j : Fin 271) : Fin 271 → F := Pi.single j 1

def coreMatrix (half alpha a b c : F) : Matrix (Fin 271) (Fin 271) F :=
  fun i j => coreMap half alpha a b c (basis j) i

theorem coreMatrix_mulVec (half alpha a b c : F) (x : Fin 271 → F) :
    (coreMatrix half alpha a b c).mulVec x = coreMap half alpha a b c x := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, coreMatrix]
  have hx : x = ∑ j : Fin 271, x j • basis j := by
    funext k
    simp [basis]
  rw [hx, map_sum]
  simp only [coreLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp [basis, coreMap_smul, mul_comm]

theorem coreMatrix_witness_mulVec (half : F) (x : Fin 271 → F) :
    (coreMatrix half 1 2 0 0).mulVec x = fun i => (2:F) * finiteBlock x i := by
  rw [coreMatrix_mulVec]
  exact funext (coreMap_witness half x)

theorem coreMatrix_witness_det_ne_zero (half : F) :
    (coreMatrix half 1 2 0 0).det ≠ 0 := by
  let h : F := (2:F)⁻¹
  have hh : (2:F)*h=1 := by simp [h]
  have hs : Function.Surjective (coreMatrix half 1 2 0 0).mulVec := by
    intro y
    refine ⟨fun i => h * finiteBlock y i, ?_⟩
    rw [coreMatrix_witness_mulVec]
    funext i
    rw [finite_scale, finite_involution, ← mul_assoc, hh, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero

#print axioms weightedQ_one
#print axioms coreMap_witness
#print axioms sourceChord_components
#print axioms sourceChord_linear
#print axioms coreMatrix_mulVec
#print axioms coreMatrix_witness_det_ne_zero
end AspisV8R19.R574SparseGCorePolynomial
