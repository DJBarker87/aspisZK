import AspisV8R19.R376SimplePointDegree

/-! A polynomial model of the selected mask Horner sum. This file bounds only
that model's degree. It does not prove correspondence with Rust execution,
source claim-table construction, or the concrete Horner implementation. -/
set_option autoImplicit false
namespace AspisR19.R382SelectedMaskDegree
open Polynomial R374SingleCoordinateDegree R376SimplePointDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

def familyLinear (z : Fin 10 → F) (j : Fin 10) (family : Nat) : F[X] :=
  ∑ i : Fin 10,
    C (((3 + 22 * i.val + family * (17 + 8 * i.val) : Nat) : F)) * line z j i

def c1Exponent (i : Fin 16) : Nat :=
  if i.val < 14 then 2 * i.val else if i.val = 14 then 13 else 25

def maskOnlyExponent (i : Fin 10) : Nat :=
  if i.val < 6 then 2 * i.val + 1 else 2 * i.val + 3

def c1TableIndex (i : Fin 16) : Fin 26 := ⟨i.val, by omega⟩
def maskOnlyTableIndex (i : Fin 10) : Fin 26 := ⟨i.val + 16, by omega⟩

def c1Term (tables : Fin 26 → Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) (i : Fin 16) : F[X] :=
  (C (basis (c1TableIndex i)) *
    claimPolynomial (tables (c1TableIndex i)) z j (0 : Fin 3)) *
      familyLinear z j 0 ^ c1Exponent i

def maskOnlyTerm (tables : Fin 26 → Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) (i : Fin 10) : F[X] :=
  (C (basis (maskOnlyTableIndex i)) *
    claimPolynomial (tables (maskOnlyTableIndex i)) z j (2 : Fin 3)) *
      familyLinear z j 0 ^ maskOnlyExponent i

def selectedShared (tables : Fin 26 → Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  (∑ i : Fin 16, c1Term tables basis z j i) +
    ∑ i : Fin 10, maskOnlyTerm tables basis z j i

def selectedMaskModel (tables : Fin 26 → Fin 1024 → F)
    (gTable : Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  selectedShared tables basis z j +
    (1 + familyLinear z j 16 ^ 26) *
      claimPolynomial gTable z j (0 : Fin 3)

def selectedMaskWrapperModel (tables : Fin 26 → Fin 1024 → F)
    (gTable : Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  selectedMaskModel tables gTable basis z j -
      (1 + familyLinear z j 16 ^ 26) * claimPolynomial gTable z j (0 : Fin 3) +
    claimPolynomial gTable z j (0 : Fin 3)

theorem c1_exponent_le (i : Fin 16) : c1Exponent i ≤ 26 := by
  unfold c1Exponent
  split_ifs <;> omega

theorem mask_only_exponent_le (i : Fin 10) : maskOnlyExponent i ≤ 26 := by
  unfold maskOnlyExponent
  split_ifs <;> omega

theorem familyLinear_degree (z : Fin 10 → F) (j : Fin 10) (family : Nat) :
    (familyLinear z j family).natDegree ≤ 1 := by
  unfold familyLinear
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_mul_le.trans
  have hline : (line z j i).natDegree ≤ 1 :=
    (line_degree z j i).trans (by split_ifs <;> omega)
  simpa only [natDegree_C, zero_add] using hline

theorem c1Term_degree (tables : Fin 26 → Fin 1024 → F)
    (basis : Fin 26 → F) (z : Fin 10 → F) (j : Fin 10) (i : Fin 16) :
    (c1Term tables basis z j i).natDegree ≤ 27 := by
  unfold c1Term
  have hclaim : (claimPolynomial (tables (c1TableIndex i)) z j (0 : Fin 3)).natDegree ≤ 1 :=
    simple_claim_degree _ _ _ _ (by decide)
  have hbase :
      (C (basis (c1TableIndex i)) *
        claimPolynomial (tables (c1TableIndex i)) z j (0 : Fin 3)).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    simpa only [natDegree_C, zero_add] using hclaim
  have hlinear := familyLinear_degree z j 0
  have hpower : (familyLinear z j 0 ^ c1Exponent i).natDegree ≤ c1Exponent i :=
    natDegree_pow_le_of_le _ hlinear
  calc
    _ ≤ (C (basis (c1TableIndex i)) *
          claimPolynomial (tables (c1TableIndex i)) z j (0 : Fin 3)).natDegree +
          (familyLinear z j 0 ^ c1Exponent i).natDegree := natDegree_mul_le _ _
    _ ≤ 1 + c1Exponent i := Nat.add_le_add hbase hpower
    _ ≤ 27 := by omega

theorem maskOnlyTerm_degree (tables : Fin 26 → Fin 1024 → F)
    (basis : Fin 26 → F) (z : Fin 10 → F) (j : Fin 10) (i : Fin 10) :
    (maskOnlyTerm tables basis z j i).natDegree ≤ 27 := by
  unfold maskOnlyTerm
  have hclaim :
      (claimPolynomial (tables (maskOnlyTableIndex i)) z j (2 : Fin 3)).natDegree ≤ 1 :=
    simple_claim_degree _ _ _ _ (by decide)
  have hbase :
      (C (basis (maskOnlyTableIndex i)) *
        claimPolynomial (tables (maskOnlyTableIndex i)) z j (2 : Fin 3)).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    simpa only [natDegree_C, zero_add] using hclaim
  have hlinear := familyLinear_degree z j 0
  have hpower : (familyLinear z j 0 ^ maskOnlyExponent i).natDegree ≤ maskOnlyExponent i :=
    natDegree_pow_le_of_le _ hlinear
  calc
    _ ≤ (C (basis (maskOnlyTableIndex i)) *
          claimPolynomial (tables (maskOnlyTableIndex i)) z j (2 : Fin 3)).natDegree +
          (familyLinear z j 0 ^ maskOnlyExponent i).natDegree := natDegree_mul_le _ _
    _ ≤ 1 + maskOnlyExponent i := Nat.add_le_add hbase hpower
    _ ≤ 27 := by omega

theorem selectedShared_degree (tables : Fin 26 → Fin 1024 → F)
    (basis : Fin 26 → F) (z : Fin 10 → F) (j : Fin 10) :
    (selectedShared tables basis z j).natDegree ≤ 27 := by
  unfold selectedShared
  apply natDegree_add_le_of_degree_le
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact c1Term_degree tables basis z j i
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact maskOnlyTerm_degree tables basis z j i

theorem explicitG_factor_degree (z : Fin 10 → F) (j : Fin 10) :
    (1 + familyLinear z j 16 ^ 26).natDegree ≤ 26 := by
  have hlinear := familyLinear_degree z j 16
  have hpower : (familyLinear z j 16 ^ 26).natDegree ≤ 26 :=
    natDegree_pow_le_of_le 26 hlinear
  exact (natDegree_add_le_of_degree_le (by simp) hpower).trans (by omega)

theorem explicitG_term_degree (gTable : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) :
    ((1 + familyLinear z j 16 ^ 26) *
      claimPolynomial gTable z j (0 : Fin 3)).natDegree ≤ 27 := by
  have hfactor := explicitG_factor_degree z j
  have hclaim : (claimPolynomial gTable z j (0 : Fin 3)).natDegree ≤ 1 :=
    simple_claim_degree _ _ _ _ (by decide)
  calc
    _ ≤ (1 + familyLinear z j 16 ^ 26).natDegree +
          (claimPolynomial gTable z j (0 : Fin 3)).natDegree := natDegree_mul_le _ _
    _ ≤ 26 + 1 := Nat.add_le_add hfactor hclaim
    _ = 27 := by norm_num

theorem selectedMaskModel_degree (tables : Fin 26 → Fin 1024 → F)
    (gTable : Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) :
    (selectedMaskModel tables gTable basis z j).natDegree ≤ 27 := by
  unfold selectedMaskModel
  exact natDegree_add_le_of_degree_le
    (selectedShared_degree tables basis z j)
    (explicitG_term_degree gTable z j)

theorem selectedMaskWrapperModel_eq (tables : Fin 26 → Fin 1024 → F)
    (gTable : Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) :
    selectedMaskWrapperModel tables gTable basis z j =
      selectedShared tables basis z j + claimPolynomial gTable z j (0 : Fin 3) := by
  unfold selectedMaskWrapperModel selectedMaskModel selectedShared
  ring

theorem selectedMaskWrapperModel_degree (tables : Fin 26 → Fin 1024 → F)
    (gTable : Fin 1024 → F) (basis : Fin 26 → F)
    (z : Fin 10 → F) (j : Fin 10) :
    (selectedMaskWrapperModel tables gTable basis z j).natDegree ≤ 27 := by
  rw [selectedMaskWrapperModel_eq]
  apply natDegree_add_le_of_degree_le
  · exact selectedShared_degree tables basis z j
  · exact simple_claim_degree _ _ _ _ (by decide)

#print axioms familyLinear_degree
#print axioms c1_exponent_le
#print axioms mask_only_exponent_le
#print axioms c1Term_degree
#print axioms maskOnlyTerm_degree
#print axioms selectedShared_degree
#print axioms explicitG_factor_degree
#print axioms explicitG_term_degree
#print axioms selectedMaskModel_degree
#print axioms selectedMaskWrapperModel_eq
#print axioms selectedMaskWrapperModel_degree
end
end AspisR19.R382SelectedMaskDegree
