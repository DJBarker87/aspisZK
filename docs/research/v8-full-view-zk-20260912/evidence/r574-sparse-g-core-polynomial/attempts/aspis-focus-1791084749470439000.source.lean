import AspisV8R19.SparseGCoreInverse
import AspisV8R17.WeightedScatter
import AspisV8R17.SourceScatter
import AspisV8R19.SparseGPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
namespace AspisV8R19.R574SparseGCorePolynomial

open AspisR19.SparseGCoreInverse AspisV8R17 AspisR19.SparseGPolynomial
open MvPolynomial

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
  simp only [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  exact chordCoefficient_components _ _ (zeroExtend (2 * 512) q) a b c r

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
  · rw [extend_add]
    change channel (extend x + extend y) (r / 4) n = _
    exact channel_add (extend x) (extend y) (r/4) n
  · simp

theorem ch_smul (n : Nat) (t : F) (x : Fin 271 → F) :
    ch n (t • x) = fun r => t * ch n x r := by
  funext r
  unfold ch
  split_ifs with h
  · rw [extend_smul]
    change channel (fun q => t * extend x q) (r / 4) n = _
    exact channel_smul t (extend x) (r/4) n
  · simp

theorem nz_add (x y : Fin 271 → F) :
    nz (x + y) = fun r => nz x r + nz y r := by
  funext r
  unfold nz
  split_ifs with h
  · simp
  · rw [extend_add]
    change channel (extend x + extend y) (r / 4) (r % 4) = _
    exact channel_add (extend x) (extend y) (r/4) (r%4)

theorem nz_smul (t : F) (x : Fin 271 → F) :
    nz (t • x) = fun r => t * nz x r := by
  funext r
  unfold nz
  split_ifs with h
  · simp
  · rw [extend_smul]
    change channel (fun q => t * extend x q) (r / 4) (r % 4) = _
    exact channel_smul t (extend x) (r/4) (r%4)

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
  rw [weightedQ_add]
  simpa only [one_mul] using
    sourceChord_linear half (weightedQ alpha x) (weightedQ alpha y)
      1 1 a b c (128+3*i.val)

theorem coreMap_smul (half alpha a b c t : F) (x : Fin 271 → F) (i : Fin 271) :
    coreMap half alpha a b c (t • x) i = t * coreMap half alpha a b c x i := by
  unfold coreMap
  rw [weightedQ_smul]
  simpa only [zero_mul, add_zero] using
    sourceChord_linear half (weightedQ alpha x) (fun _ => 0) t 0 a b c
      (128+3*i.val)

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
  (coreLinearMap half alpha a b c).toMatrix'

theorem coreMatrix_apply (half alpha a b c : F) (i j : Fin 271) :
    coreMatrix half alpha a b c i j = coreMap half alpha a b c (basis j) i := rfl

theorem coreMatrix_mulVec (half alpha a b c : F) (x : Fin 271 → F) :
    (coreMatrix half alpha a b c).mulVec x = coreMap half alpha a b c x := by
  change (LinearMap.toMatrix' (coreLinearMap half alpha a b c)).mulVec x =
    (coreLinearMap half alpha a b c) x
  exact LinearMap.toMatrix'_mulVec (coreLinearMap half alpha a b c) x

theorem coreMatrix_witness_mulVec (half : F) (x : Fin 271 → F) :
    (coreMatrix half 1 2 0 0).mulVec x = fun i => (2:F) * finiteBlock x i := by
  rw [coreMatrix_mulVec]
  funext i
  exact coreMap_witness half x i

theorem coreMatrix_witness_det_ne_zero (half : F) :
    (coreMatrix half 1 2 0 0).det ≠ 0 := by
  let h : F := (2:F)⁻¹
  have h2 : (2:F) ≠ 0 := NeZero.ne _
  have hh : (2:F)*h=1 := by
    dsimp [h]
    field_simp
  have hs : Function.Surjective (coreMatrix half 1 2 0 0).mulVec := by
    intro y
    refine ⟨fun i => h * finiteBlock y i, ?_⟩
    rw [coreMatrix_witness_mulVec]
    funext i
    rw [finite_scale, finite_involution, ← mul_assoc, hh, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero

abbrev CorePoly (F : Type*) [CommSemiring F] := MvPolynomial (Fin 4) F

def coreAssignment (alpha a b c : F) : Fin 4 → F :=
  fun i => if i.val = 0 then alpha else if i.val = 1 then a else if i.val = 2 then b else c

def sourceBasisValue (half : F) (q : Nat → F) (u v w : F) (i : Fin 271) : F :=
  sourceChord half q u v w (128 + 3 * i.val)

noncomputable def componentPolynomial (half : F) (u v w : F) (q0 q1 q2 q3 : Nat → F)
    (i : Fin 271) : CorePoly F :=
  C (sourceBasisValue half q0 u v w i) - X (0:Fin 4) * C (sourceBasisValue half q1 u v w i) -
    X (0:Fin 4) ^ 2 * C (sourceBasisValue half q2 u v w i) -
    X (0:Fin 4) ^ 3 * C (sourceBasisValue half q3 u v w i)

noncomputable def coreEntryPolynomial (half : F) (i j : Fin 271) : CorePoly F :=
  X (1:Fin 4) * componentPolynomial half 1 0 0 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)) i +
  X (2:Fin 4) * componentPolynomial half 0 1 0 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)) i +
  X (3:Fin 4) * componentPolynomial half 0 0 1 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)) i

noncomputable def corePolynomialMatrix (half : F) : Matrix (Fin 271) (Fin 271) (CorePoly F) :=
  coreEntryPolynomial half

theorem sourceChord_four (half alpha : F) (q0 q1 q2 q3 : Nat → F)
    (a b c : F) (r : Nat) :
    sourceChord half (fun n => q0 n-alpha*q1 n-alpha^2*q2 n-alpha^3*q3 n) a b c r =
      sourceChord half q0 a b c r - alpha * sourceChord half q1 a b c r -
        alpha^2 * sourceChord half q2 a b c r - alpha^3 * sourceChord half q3 a b c r := by
  let q12 := fun n => q0 n + (-alpha) * q1 n
  let q123 := fun n => q12 n + (-alpha^2) * q2 n
  let q1234 := fun n => q123 n + (-alpha^3) * q3 n
  have hq : (fun n => q0 n-alpha*q1 n-alpha^2*q2 n-alpha^3*q3 n) = q1234 := by
    funext n
    simp only [q12, q123, q1234]
    ring
  rw [hq]
  have h3 := sourceChord_linear half q123 q3 1 (-alpha^3) a b c r
  simp only [one_mul, neg_mul, sub_eq_add_neg] at h3
  dsimp [q1234] at h3
  rw [h3]
  have h2 := sourceChord_linear half q12 q2 1 (-alpha^2) a b c r
  simp only [one_mul, neg_mul, sub_eq_add_neg] at h2
  dsimp [q123] at h2
  rw [h2]
  have h1 := sourceChord_linear half q0 q1 1 (-alpha) a b c r
  simp only [one_mul, neg_mul, sub_eq_add_neg] at h1
  dsimp [q12] at h1
  rw [h1]
  ring

theorem sourceChord_weighted (half alpha : F) (x : Fin 271 → F)
    (a b c : F) (r : Nat) :
    sourceChord half (weightedQ alpha x) a b c r =
      sourceChord half (nz x) a b c r - alpha * sourceChord half (ch 1 x) a b c r -
        alpha ^ 2 * sourceChord half (ch 2 x) a b c r -
        alpha ^ 3 * sourceChord half (ch 3 x) a b c r := by
  exact sourceChord_four half alpha (nz x) (ch 1 x) (ch 2 x) (ch 3 x) a b c r

theorem componentPolynomial_eval (half alpha a b c u v w : F) (q0 q1 q2 q3 : Nat → F)
    (i : Fin 271) :
    eval (coreAssignment alpha a b c) (componentPolynomial half u v w q0 q1 q2 q3 i) =
      sourceChord half (fun n => q0 n - alpha*q1 n-alpha^2*q2 n-alpha^3*q3 n)
        u v w (128+3*i.val) := by
  simp [componentPolynomial, sourceBasisValue, coreAssignment, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X]
  rw [← sourceChord_four half alpha q0 q1 q2 q3 u v w (128+3*i.val)]

theorem coreEntryPolynomial_eval (half alpha a b c : F) (i j : Fin 271) :
    eval (coreAssignment alpha a b c) (coreEntryPolynomial half i j) =
      coreMatrix half alpha a b c i j := by
  rw [coreMatrix_apply]
  simp only [coreEntryPolynomial, eval_add, eval_mul]
  rw [componentPolynomial_eval half alpha a b c 1 0 0,
    componentPolynomial_eval half alpha a b c 0 1 0,
    componentPolynomial_eval half alpha a b c 0 0 1]
  simp only [eval_X, coreAssignment]
  unfold coreMap
  rw [sourceChord_components]
  simp only [weightedQ]
  ring

theorem corePolynomialMatrix_eval (half alpha a b c : F) :
    (eval (coreAssignment alpha a b c)).mapMatrix (corePolynomialMatrix half) =
      coreMatrix half alpha a b c := by
  ext i j
  exact coreEntryPolynomial_eval half alpha a b c i j

theorem corePolynomialDet_eval (half alpha a b c : F) :
    eval (coreAssignment alpha a b c) (corePolynomialMatrix half).det =
      (coreMatrix half alpha a b c).det := by
  rw [(eval (coreAssignment alpha a b c)).map_det, corePolynomialMatrix_eval]

theorem corePolynomialDet_ne_zero (half : F) :
    (corePolynomialMatrix half).det ≠ 0 := by
  intro hzero
  have he := corePolynomialDet_eval half 1 2 0 0
  rw [hzero, map_zero] at he
  exact coreMatrix_witness_det_ne_zero half he.symm

theorem componentPolynomial_degree (half : F) (q0 q1 q2 q3 : Nat → F)
    (i : Fin 271) :
    (componentPolynomial half q0 q1 q2 q3 i).totalDegree ≤ 3 := by
  unfold componentPolynomial
  have hc (x : F) : (C x : CorePoly F).totalDegree ≤ 0 := by simp
  have hx (n : Nat) : ((X (0:Fin 4) : CorePoly F)^n).totalDegree ≤ n := by
    have hpow := totalDegree_pow (X (0:Fin 4) : CorePoly F) n
    simpa using hpow.trans (Nat.mul_le_mul_left n
      (by simp : (X (0:Fin 4) : CorePoly F).totalDegree ≤ 1))
  have hm (n : Nat) (q : Nat → F) :
      ((X (0:Fin 4) : CorePoly F)^n * C (sourceBasisValue half q i)).totalDegree ≤ n := by
    exact (totalDegree_mul _ _).trans (Nat.add_le_add (hx n) (hc _))
  have h0 : (C (sourceBasisValue half q0 i) : CorePoly F).totalDegree ≤ 0 := hc _
  have h1 := hm 1 q1
  have h2 := hm 2 q2
  have h3 := hm 3 q3
  have h1' : (X (0:Fin 4) * C (sourceBasisValue half q1 i)).totalDegree ≤ 1 := by
    simpa using h1
  have h2' : (X (0:Fin 4)^2 * C (sourceBasisValue half q2 i)).totalDegree ≤ 2 := by
    simpa using h2
  have h3' : (X (0:Fin 4)^3 * C (sourceBasisValue half q3 i)).totalDegree ≤ 3 := by
    simpa using h3
  have hab : (C (sourceBasisValue half q0 i) - X (0:Fin 4) * C (sourceBasisValue half q1 i)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (h0.trans (by omega)) h1')
  have habc : ((C (sourceBasisValue half q0 i) - X (0:Fin 4) * C (sourceBasisValue half q1 i)) -
      X (0:Fin 4) ^ 2 * C (sourceBasisValue half q2 i)).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (hab.trans (by omega)) h2')
  exact ((totalDegree_sub _ _).trans (max_le habc h3')).trans (by omega)

theorem coreEntryPolynomial_degree (half : F) (i j : Fin 271) :
    (coreEntryPolynomial half i j).totalDegree ≤ 4 := by
  unfold coreEntryPolynomial
  have hcomp : ∀ q0 q1 q2 q3,
      (componentPolynomial half q0 q1 q2 q3 i).totalDegree ≤ 3 :=
    fun _ _ _ _ => componentPolynomial_degree half _ _ _ _ i
  have hx (n : Fin 4) : ((X n : CorePoly F)).totalDegree ≤ 1 := by simp
  have hm (n : Fin 4) (q0 q1 q2 q3 : Nat → F) :
      (X n * componentPolynomial half q0 q1 q2 q3 i).totalDegree ≤ 4 :=
    (totalDegree_mul _ _).trans (Nat.add_le_add (hx n) (hcomp q0 q1 q2 q3))
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (hm 1 _ _ _ _) (hm 2 _ _ _ _)))
    (hm 3 _ _ _ _))

theorem corePolynomialDet_degree (half : F) :
    (corePolynomialMatrix half).det.totalDegree ≤ 1084 := by
  simpa using AspisV8R17.minor_totalDegree (corePolynomialMatrix half) 4
    (coreEntryPolynomial_degree half)

#print axioms weightedQ_one
#print axioms coreMap_witness
#print axioms sourceChord_components
#print axioms sourceChord_linear
#print axioms coreMatrix_mulVec
#print axioms coreMatrix_witness_det_ne_zero
#print axioms coreEntryPolynomial_eval
#print axioms corePolynomialDet_ne_zero
#print axioms coreEntryPolynomial_degree
#print axioms corePolynomialDet_degree
end AspisV8R19.R574SparseGCorePolynomial
