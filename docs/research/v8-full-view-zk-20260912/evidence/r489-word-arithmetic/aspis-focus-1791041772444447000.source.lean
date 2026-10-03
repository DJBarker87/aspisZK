import AspisV8R19.R195CountedSliceFoldArithmetic

set_option autoImplicit false

namespace AspisV8R19.R489WordArithmetic

open Aeneas Aeneas.Std Result

theorem div_four (n : Usize) :
    ∃ q : Usize, n / (4#usize) = .ok q ∧ q.val = n.val / 4 := by
  have hfour : (4#usize : Usize).val ≠ 0 := by decide
  obtain ⟨q, hrun, hval⟩ := UScalar.div_spec n (y := 4#usize) hfour
  exact ⟨q, hrun, by simpa using hval⟩

theorem rem_four (n : Usize) :
    ∃ r : Usize, n % (4#usize) = .ok r ∧ r.val = n.val % 4 := by
  have hfour : (4#usize : Usize).val ≠ 0 := by decide
  have hspec := UScalar.rem_spec n hfour
  obtain ⟨r, hrun, hval⟩ := spec_imp_exists hspec
  exact ⟨r, hrun, by simpa using hval⟩

theorem wrapping_mul_one (q : Usize) :
    UScalar.wrapping_mul q (1#usize) = q := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.wrapping_mul_val_eq]

theorem div_four_one : (4#usize) / (1#usize) = .ok (4#usize) := by
  have h : (1#usize : Usize).val ≠ 0 := by decide
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec (4#usize) (y := 1#usize) h
  have heq : z = 4#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hv
  simpa [heq] using hz

theorem div_one_one : (1#usize) / (1#usize) = .ok (1#usize) := by
  have h : (1#usize : Usize).val ≠ 0 := by decide
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec (1#usize) (y := 1#usize) h
  have heq : z = 1#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hv
  simpa [heq] using hz

theorem one_nonzero_and_divisor_guards :
    (1#usize : Usize).val ≠ 0 ∧
    decide ((1#usize : Usize).val == 0) = false ∧
    decide ((4#usize : Usize).val == 0) = false := by
  decide

theorem div_rem_partition (n : Usize) :
    n.val / 4 * 4 + n.val % 4 = n.val ∧ n.val % 4 < 4 := by
  constructor
  · simpa [Nat.mul_comm] using (Nat.div_add_mod n.val 4)
  · exact Nat.mod_lt n.val (by omega)

#print axioms div_four
#print axioms rem_four
#print axioms wrapping_mul_one
#print axioms div_four_one
#print axioms div_one_one
#print axioms one_nonzero_and_divisor_guards
#print axioms div_rem_partition

end AspisV8R19.R489WordArithmetic
