import R1Z.ProverCommitBoundarySum49
import R1Z.ProverCommitLimbBytes47
import R1Z.ProverCommitInterpolationPoly48
/-! Four-limb boundary owner and exact polynomial boundary value. The Kani
accumulator split and the separately proved current reducer bind its source. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitBoundaryValue49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open AspisV8R15.ExactTowerBase (M31Exact)
open ProverCommitLimbBytes47 (sourceLimb)

def component (x : QM31Exact) : Fin 4 → M31Exact := ![x.re.re,x.re.im,x.im.re,x.im.im]

theorem component_decode (q : Old.Q) (k : Fin 4) :
    component (decode q) k=((sourceLimb q k).val : M31Exact) := by fin_cases k <;> rfl

theorem component_add (x y : QM31Exact) (k : Fin 4) :
    component (x+y) k=component x k+component y k := by fin_cases k <;> rfl

theorem component_twice (x : QM31Exact) (k : Fin 4) :
    component (2*x) k=2*component x k := by
  rw [two_mul,component_add,two_mul]

def sum (p : Nat → Old.Q) : Nat → Nat → QM31Exact
 | 0,_ => 0
 | n+1,j => decode (p j)+sum p n (j+1)

theorem component_sum (p : Nat → Old.Q) (n j : Nat) (k : Fin 4) :
    component (sum p n j) k=(ProverCommitBoundarySum49.sum (fun i => sourceLimb (p i) k) n j : M31Exact) := by
  induction n generalizing j with
  | zero => fin_cases k <;> rfl
  | succ n ih => rw [sum,component_add,component_decode,ih,ProverCommitBoundarySum49.sum,Nat.cast_add]

def word (p : Nat → Old.Q) (k : Fin 4) : U32 :=
  Classical.choose (ProverCommitBoundarySum49.limb_value (fun i => sourceLimb (p i) k))

theorem word_spec (p : Nat → Old.Q) (k : Fin 4) :
    Boundary49.limb (ProverCommitBoundarySum49.array (fun i => sourceLimb (p i) k))=ok (word p k) ∧
      (word p k).val=(2*(sourceLimb (p 0) k).val+
        ProverCommitBoundarySum49.sum (fun i => sourceLimb (p i) k) 27 1)%AspisCircleGroupOrder.P ∧
      (word p k).val<AspisCircleGroupOrder.P :=
  Classical.choose_spec (ProverCommitBoundarySum49.limb_value (fun i => sourceLimb (p i) k))

def output (p : Nat → Old.Q) : Old.Q := ⟨⟨word p 0,word p 1⟩,⟨word p 2,word p 3⟩⟩

theorem output_canonical (p : Nat → Old.Q) : Canonical (output p) :=
  ⟨⟨(word_spec p 0).2.2,(word_spec p 1).2.2⟩,⟨(word_spec p 2).2.2,(word_spec p 3).2.2⟩⟩

theorem output_limb (p : Nat → Old.Q) (k : Fin 4) : sourceLimb (output p) k=word p k := by
  fin_cases k <;> rfl

theorem output_value (p : Nat → Old.Q) : decode (output p)=2*decode (p 0)+sum p 27 1 := by
  have h (k : Fin 4) : component (decode (output p)) k=component (2*decode (p 0)+sum p 27 1) k := by
    rw [component_decode,output_limb,(word_spec p k).2.1]
    change (((2*(sourceLimb (p 0) k).val+ProverCommitBoundarySum49.sum (fun i => sourceLimb (p i) k) 27 1)%
      AspisCircleGroupOrder.P : Nat) : ZMod AspisCircleGroupOrder.P)=_
    rw [ZMod.natCast_mod,component_add,component_twice,component_decode,component_sum,Nat.cast_add,Nat.cast_mul]
    rfl
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact h 0
    · exact h 1
  · apply QuadraticAlgebra.ext
    · exact h 2
    · exact h 3

theorem sum_poly (p : Nat → Old.Q) (n j : Nat) :
    sum p n j=∑ k ∈ Finset.range n, decode (p (j+k)) := by
  induction n generalizing j with
  | zero => simp only [sum,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [sum,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega

#print axioms component_decode
#print axioms component_add
#print axioms component_twice
#print axioms component_sum
#print axioms word_spec
#print axioms output_canonical
#print axioms output_limb
#print axioms output_value
#print axioms sum_poly
end R1Z.ProverCommitBoundaryValue49
