import R1Z.ProverCommitBooleanEnum49
import Mathlib.Data.Fin.Tuple.Basic
/-! Native prefix/suffix row formula decodes to exactly appended Boolean bits. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseConcat50
open ProverCommitBooleanEnum49

theorem bound (m n a b : Nat) (ha : a<2^m) (hb : b<2^n) :
    a*2^n+b<2^(m+n) := by
  calc
    _ < (a+1)*2^n := by rw [Nat.add_mul,Nat.one_mul];omega
    _ ≤ 2^m*2^n := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_add 2 m n).symm

def concat (m n : Nat) (a : Fin (2^m)) (b : Fin (2^n)) : Fin (2^(m+n)) :=
  ⟨a.val*2^n+b.val,bound m n a.val b.val a.isLt b.isLt⟩

theorem high (m n : Nat) (a : Fin (2^m)) (b : Fin (2^n)) (i : Fin m) :
    tail (m+n) (concat m n a b) (i.castAdd n)=tail m a i := by
  unfold tail concat
  simp only [Fin.val_mk,Fin.val_castAdd]
  rw [Nat.mul_comm a.val (2^n),Nat.testBit_two_pow_mul_add a.val b.isLt]
  rw [if_neg (by have := i.isLt;omega)]
  congr 1
  have := i.isLt
  omega

theorem low (m n : Nat) (a : Fin (2^m)) (b : Fin (2^n)) (i : Fin n) :
    tail (m+n) (concat m n a b) (i.natAdd m)=tail n b i := by
  unfold tail concat
  simp only [Fin.val_mk,Fin.val_natAdd]
  rw [Nat.mul_comm a.val (2^n),Nat.testBit_two_pow_mul_add a.val b.isLt]
  rw [if_pos (by have := i.isLt;omega)]
  congr 1
  omega

theorem bits (m n : Nat) (a : Fin (2^m)) (b : Fin (2^n)) :
    tail (m+n) (concat m n a b)=Fin.append (tail m a) (tail n b) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left,high]
  · rw [Fin.append_right,low]

#print axioms bound
#print axioms high
#print axioms low
#print axioms bits
end R1Z.ProverCommitSparseConcat50
