import S9TwoDualSourceBaseV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9TwoDualSourcePrivateV1
open AspisR1
open AspisR1S9TwoDualFoldExpansionV1
open AspisR1S9TwoDualSourceBaseV1
open scoped BigOperators
variable {K : Type} [Field K]

/-- Existing S2 private row: two28-entry seed-power blocks, zero elsewhere. -/
def privateRow (q0 q1 : K) (i : Fin 1024) : K :=
  if i.val<56 then (if i.val<28 then q0^(i.val%28) else q1^(i.val%28)) else 0

theorem private_two_dual_first (a0 a1 q0 q1 : K) (d : Fin 4) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (privateRow q0 q1)) (Fin.castAdd 60 d)=
      AspisR1.S3S9CurrentSourceModel.oldS9Weight (powers a0) (powers a1) RoundPairing.quarter q0 q1 d := by
  rw [two_dual_fold_1024_64]
  unfold AspisR1.S3S9CurrentSourceModel.oldS9Weight
  apply Finset.sum_congr rfl
  intro s _
  change (if 16*d.val+s.val<56 then
      (if 16*d.val+s.val<28 then q0^((16*d.val+s.val)%28) else q1^((16*d.val+s.val)%28)) else 0)*
      RoundPairing.quarter^2*a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4)=
    if 16*d.val+s.val<56 then lowWeight a0 a1 s*
      (if 16*d.val+s.val<28 then q0^((16*d.val+s.val)%28) else q1^((16*d.val+s.val)%28)) else 0
  by_cases h56 : 16*d.val+s.val<56
  · rw [if_pos h56,if_pos h56,low_weight_formula]
    ring
  · simp only [if_neg h56,zero_mul]

theorem private_two_dual_first_original (a0 a1 q0 q1 : K) (d : Fin 4) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (privateRow q0 q1)) (Fin.castAdd 60 d)=
      AspisR1.S2LibraFactoredIdentity.original
        (AspisR1.S2LibraFactoredIdentity.scaled (powers a0) RoundPairing.quarter)
        (AspisR1.S2LibraFactoredIdentity.scaled (powers a1) RoundPairing.quarter) q0 q1 d := by
  rw [private_two_dual_first]
  exact AspisR1.S3S9CurrentSourceModel.old_s9_weight_eq_reference
    (powers a0) (powers a1) RoundPairing.quarter q0 q1 d

/-- Symbolic support bound, not a1024-coordinate finite check. -/
theorem private_two_dual_tail_zero (a0 a1 q0 q1 : K) (d : Fin 64) (hd : 4≤d.val) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (privateRow q0 q1)) d=0 := by
  rw [two_dual_fold_1024_64]
  apply Finset.sum_eq_zero
  intro s _
  have hnot : ¬(blockIndex d s).val<56 := by
    change ¬16*d.val+s.val<56
    omega
  simp only [privateRow,if_neg hnot,zero_mul]

/-- All60 tail coordinates vanish by support; the four surviving coefficients
are the existing ORIGINAL formula. No coefficient factorization is reproved. -/
theorem private_two_dual_dot_original (a0 a1 q0 q1 : K) (f : Fin 64 → K) :
    RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (privateRow q0 q1)))=
      ∑d : Fin 4,f (Fin.castAdd 60 d)*AspisR1.S2LibraFactoredIdentity.original
        (AspisR1.S2LibraFactoredIdentity.scaled (powers a0) RoundPairing.quarter)
        (AspisR1.S2LibraFactoredIdentity.scaled (powers a1) RoundPairing.quarter) q0 q1 d := by
  unfold RoundPairing.dot
  rw [Fin.sum_univ_add (a:=4) (b:=60)]
  have htail : (∑j : Fin 60,f (Fin.natAdd 4 j)*
      RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (privateRow q0 q1)) (Fin.natAdd 4 j))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [private_two_dual_tail_zero a0 a1 q0 q1 (Fin.natAdd 4 j) (by change 4≤4+j.val;omega),mul_zero]
  rw [htail,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  rw [private_two_dual_first_original]

#print axioms private_two_dual_first
#print axioms private_two_dual_first_original
#print axioms private_two_dual_tail_zero
#print axioms private_two_dual_dot_original
end AspisR1S9TwoDualSourcePrivateV1
end
