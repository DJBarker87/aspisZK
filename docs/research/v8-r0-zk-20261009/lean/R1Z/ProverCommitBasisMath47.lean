import AspisFormal.V5FriNaturalBasisRadix4
/-! Symbolic block identity for basis::values. No concrete 512-element basis
or recurrence cell is normalized. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBasisMath47
open AspisCircleTensorBinding AspisV5FriNaturalBasisRadix4
variable {K : Type} [CommRing K]

theorem natural_zero (x : K) : naturalLineValue x 0=1 := by
  simp [naturalLineValue]

theorem natural_one (x : K) : naturalLineValue x 1=x := by
  simp [naturalLineValue,doubledFactor]

/-- Appending the next power-of-two block multiplies the old block by the
current doubling factor, exactly the source table's inner assignment. -/
theorem block (depth : Nat) (x : K) (j : Nat) (hj : j<2^depth) :
    naturalLineValue x (2^depth+j)=naturalLineValue x j*doubledFactor x depth := by
  induction depth generalizing x j with
  | zero =>
    have hz : j=0 := by simp only [pow_zero] at hj;omega
    subst j
    simp only [pow_zero,Nat.add_zero,natural_one,natural_zero,doubledFactor,one_mul]
  | succ depth ih =>
    have hp : 2^(depth+1)=2*2^depth := by rw [pow_succ];omega
    have hq : j/2<2^depth := by rw [hp] at hj;omega
    have hf : doubledFactor x (depth+1)=doubledFactor (doubledFactor x 1) depth := by
      rw [show depth+1=1+depth by omega,doubledFactor_add]
    by_cases he : j%2=0
    · have hj' : j=2*(j/2) := by omega
      have hs : 2^(depth+1)+j=2*(2^depth+j/2) := by rw [hp,hj'];omega
      have hv : naturalLineValue x j=naturalLineValue (doubledFactor x 1) (j/2) := by
        calc
          naturalLineValue x j=naturalLineValue x (2*(j/2)) := congrArg (naturalLineValue x) hj'
          _ = _ := naturalLineValue_two_mul _ _
      rw [hs,naturalLineValue_two_mul,ih _ _ hq,hv,hf]
    · have ho : j%2=1 := by omega
      have hj' : j=2*(j/2)+1 := by omega
      have hs : 2^(depth+1)+j=2*(2^depth+j/2)+1 := by rw [hp,hj'];omega
      have hv : naturalLineValue x j=x*naturalLineValue (doubledFactor x 1) (j/2) := by
        calc
          naturalLineValue x j=naturalLineValue x (2*(j/2)+1) := congrArg (naturalLineValue x) hj'
          _ = _ := naturalLineValue_two_mul_add_one _ _
      rw [hs,naturalLineValue_two_mul_add_one,ih _ _ hq,hv,hf]
      ring

#print axioms natural_zero
#print axioms natural_one
#print axioms block
end R1Z.ProverCommitBasisMath47
