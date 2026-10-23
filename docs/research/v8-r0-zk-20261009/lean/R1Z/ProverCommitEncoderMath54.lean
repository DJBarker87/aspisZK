import R1Z.ProverCommitEncoderEval54
import R1Z.ProverCommitBasisMath47
/-! Symbolic natural-basis meaning of the encoder recurrence. No concrete
256-cell sum is reduced by the kernel. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderMath54
open AspisCircleTensorBinding AspisV5FriNaturalBasisRadix4
open ProverCommitEncoderEval54
variable {K : Type} [CommRing K]

def evaluate : Nat → (Nat → K) → (Nat → K) → Nat → K
 | 0,c,_,_ => c 0
 | h+1,c,n,d => evaluate h (fun i => c (2*i)) n (d+1)+n d*evaluate h (fun i => c (2*i+1)) n (d+1)

theorem wide_evaluate (h : Nat) (c n : Nat → ProverCommitWideOps48.Exact) (d : Nat) :
    eval h c n d=evaluate h c n d := by
  induction h generalizing c d with
  | zero => rfl
  | succ h ih => simp only [eval,evaluate,ih]

theorem sum_even_odd (n : Nat) (f : Nat → K) :
    (∑ i ∈ Finset.range (2*n), f i)=
      (∑ i ∈ Finset.range n, f (2*i))+(∑ i ∈ Finset.range n, f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [Finset.sum_range_succ,ih]
    ring

theorem nodes_congr (h : Nat) (c n m : Nat → K) (d : Nat)
    (he : ∀ k, k<h → n (d+k)=m (d+k)) :
    evaluate h c n d=evaluate h c m d := by
  induction h generalizing c d with
  | zero => rfl
  | succ h ih =>
    have hhead : n d=m d := by simpa only [Nat.add_zero] using he 0 (by omega)
    have htail : ∀ k, k<h → n (d+1+k)=m (d+1+k) := by
      intro k hk
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using he (k+1) (by omega)
    simp only [evaluate,hhead,ih _ _ htail]

theorem evaluate_natural (h : Nat) (c : Nat → K) (x : K) (d : Nat) :
    evaluate h c (doubledFactor x) d=
      ∑ i ∈ Finset.range (2^h), c i*naturalLineValue (doubledFactor x d) i := by
  induction h generalizing c d with
  | zero => simp [evaluate,ProverCommitBasisMath47.natural_zero]
  | succ h ih =>
    rw [evaluate,ih,ih,show 2^(h+1)=2*2^h by rw [pow_succ,Nat.mul_comm],sum_even_odd]
    simp only [naturalLineValue_two_mul,naturalLineValue_two_mul_add_one]
    have hd : doubledFactor (doubledFactor x d) 1=doubledFactor x (d+1) :=
      (doubledFactor_add x d 1).symm
    rw [hd,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

#print axioms wide_evaluate
#print axioms sum_even_odd
#print axioms nodes_congr
#print axioms evaluate_natural
end R1Z.ProverCommitEncoderMath54
