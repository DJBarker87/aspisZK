/- Current sparse-G selected source minor. No challenge-law premise. -/
import AspisV8R17.ActiveEntry
import AspisV8R17.MinorDegree
import AspisV8R19.SparseGChordWitness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AspisR19.SparseGPolynomial
open AspisV8R17 AspisR19.SparseGCoreInverse AspisR19.SparseGChordWitness
open MvPolynomial
noncomputable section
variable {F : Type*} [CommRing F] [Nontrivial F]

def node (i : Fin 271) : Nat := 128+3*i.val
def base (j : Fin 271) : Nat := 4*(node j/4)
def slot (j : Fin 271) : Nat := if node j%4=0 then 1 else node j%4

theorem column_binding (j : Fin 271) :
    base j=4*(22+selectedColumn j/3) ∧ slot j=1+selectedColumn j%3 := by
  simp only [base,slot,node,selectedColumn]
  split <;> constructor <;> omega

def entry (half alpha a b c : F) (i j : Fin 271) : F :=
  sourceChord half
    (fun r => unitVector (base j+slot j) r-alpha^slot j*unitVector (base j) r)
    a b c (node i)

def polyEntry (half : F) (i j : Fin 271) : ActivePoly F :=
  activeEntry (sourceBasisConstants half (unitVector (base j+slot j)) (node i))
    (sourceBasisConstants half (unitVector (base j)) (node i)) (slot j)

def polyMinor (half : F) : Matrix (Fin 271) (Fin 271) (ActivePoly F) := polyEntry half
def minor (half alpha a b c : F) : Matrix (Fin 271) (Fin 271) F := entry half alpha a b c

theorem entry_eval (half alpha u v : F) (i j : Fin 271) :
    eval (activeAssignment alpha u v) (polyEntry half i j) =
      entry half alpha (1+u*v) (u*v-1) (-(u+v)) i j := by
  exact sourceEntry_eval _ _ _ _ _ _ _ _

theorem entry_degree (half : F) (i j : Fin 271) :
    (polyEntry half i j).totalDegree ≤ 5 := by
  apply sourceEntry_degree
  unfold slot
  split <;> omega

theorem minor_eval (half alpha u v : F) :
    (eval (activeAssignment alpha u v)).mapMatrix (polyMinor half) =
      minor half alpha (1+u*v) (u*v-1) (-(u+v)) := by
  ext i j
  exact entry_eval _ _ _ _ _ _

theorem determinant_eval (half alpha u v : F) :
    eval (activeAssignment alpha u v) (polyMinor half).det =
      (minor half alpha (1+u*v) (u*v-1) (-(u+v))).det := by
  rw [(eval (activeAssignment alpha u v)).map_det,minor_eval]

theorem determinant_degree (half : F) : (polyMinor half).det.totalDegree ≤ 1355 := by
  have hd := minor_totalDegree (polyMinor half) 5 (fun i j => entry_degree half i j)
  simpa using hd

theorem source_scalar (half a : F) (q : Nat → F) (r : Nat) (hr : r<1024) :
    sourceChord half q a 0 0 r = a*q r := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [scalar_chord,zeroExtend_retained 1024 q r hr]

def delta (r : Nat) (j : Fin 271) : F := if r=j.val then 1 else 0

theorem sparse_read (i j : Fin 271) :
    unitVector (base j+slot j) (node i) - unitVector (base j) (node i) =
      (if i.val%4=0 then -delta i.val j-delta (i.val+1) j else delta i.val j : F) := by
  unfold unitVector base slot node delta
  split_ifs <;> first | omega | ring

theorem delta_sum (v : Fin 271 → F) (r : Nat) :
    (∑ j, delta r j*v j) = extend v r := by
  by_cases hr : r<271
  · let k : Fin 271 := ⟨r,hr⟩
    have h : ∀ j : Fin 271, r=j.val ↔ k=j := by
      intro j
      change k.val=j.val ↔ k=j
      exact Fin.ext_iff.symm
    simp [delta,h,extend,hr,k]
  · have h : ∀ j : Fin 271, r≠j.val := by intro j; omega
    simp [delta,h,extend,hr]

theorem witness_mulVec (half : F) (v : Fin 271 → F) :
    (minor half 1 2 0 0).mulVec v = fun i => (2:F)*finiteBlock v i := by
  funext i
  have hi : node i<1024 := by unfold node; omega
  simp only [Matrix.mulVec,dotProduct,minor,entry,source_scalar half 2 _ _ hi,
    one_pow,one_mul,sparse_read]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  simp only [finiteBlock,block]
  split
  · simp only [sub_mul,neg_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib,delta_sum]
  · rw [delta_sum]

theorem witness_det_ne_zero (half h : F) (hh : (2:F)*h=1) :
    (minor half 1 2 0 0).det ≠ 0 := by
  have hs : Function.Surjective (minor half 1 2 0 0).mulVec := by
    intro v
    refine ⟨fun i => h*finiteBlock v i, ?_⟩
    rw [witness_mulVec]
    exact scaled_block_inverse h hh v
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero

theorem polynomial_ne_zero (half u h : F) (hu : u*u = -1) (hh : (2:F)*h=1) :
    (polyMinor half).det ≠ 0 := by
  intro hz
  have he := determinant_eval half 1 u (-u)
  have hp : u*(-u)=1 := by rw [mul_neg,hu,neg_neg]
  have ht : (1:F)+1=2 := by ring
  rw [hz,map_zero,hp,ht,sub_self,add_neg_cancel,neg_zero] at he
  exact witness_det_ne_zero half h hh he.symm

theorem core_surjective_outside_zero_set {K : Type*} [Field K]
    (half alpha u v : K)
    (good : eval (activeAssignment alpha u v) (polyMinor half).det ≠ 0) :
    Function.Surjective (minor half alpha (1+u*v) (u*v-1) (-(u+v))).mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [← determinant_eval]
  exact good

#print axioms column_binding
#print axioms entry_eval
#print axioms entry_degree
#print axioms minor_eval
#print axioms determinant_eval
#print axioms determinant_degree
#print axioms source_scalar
#print axioms sparse_read
#print axioms delta_sum
#print axioms witness_mulVec
#print axioms witness_det_ne_zero
#print axioms polynomial_ne_zero
#print axioms core_surjective_outside_zero_set
end
end AspisR19.SparseGPolynomial
