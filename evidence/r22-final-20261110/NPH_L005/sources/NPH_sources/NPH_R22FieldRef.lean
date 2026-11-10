import R22TotalCheckedComposition

/-! NPH_ (R22 re-pin at 4bb3b3f): reference M31 kernels, written with the exact
statement shapes of the gate's checked (overflow-checks ON) Aeneas bodies of frozen
crates/aspis-core/src/field.rs (reduce_u64 31:0-44:1, M31::add 62:4-88:5 non-r91 branch,
M31::sub 94:4-119:5, M31::neg 122:4-130:5, M31::mul 133:4-137:5). The NPH_R22FieldCopies
module proves each gate copy definitionally equal to these references.

For each reference this module gives
* an explicit operational tree (R22TotalCheckedComposition.Code) whose checked semantics
  is the reference (no supplied Translation, the 2021 R22TotalReducerExecution pattern);
* checked totality on the stated domain (all inputs, or canonical limbs < P);
* the composed R22 corollary: no executed checked operation overflows and the wrapping
  interpretation of the same tree returns the checked result.
Standard axioms only; no premise on the field; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22FieldRef
open Aeneas Aeneas.Std Result AspisR1.R22TotalCheckedComposition

def P32 : U32 := 2147483647#u32
theorem P32_val : P32.val = 2147483647 := rfl

/-! ## Primitive success laws (re-stated from the 2021 R22TotalUnsignedPrimitives, which is
not in the TAS_FinalB closure; same proofs against the pinned Aeneas Std). -/

theorem add_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : (x + y : Result (UScalar ty)) = ok z) :
    UScalar.wrapping_add x y = z ∧ x.val + y.val < 2^ty.numBits := by
  have he := UScalar.add_equiv x y
  simp only [h] at he
  refine ⟨?_, he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv + y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem sub_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : (x - y : Result (UScalar ty)) = ok z) :
    UScalar.wrapping_sub x y = z ∧ y.val ≤ x.val := by
  have he := UScalar.sub_equiv x y
  simp only [h] at he
  refine ⟨?_, he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv - y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem mul_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : (x * y : Result (UScalar ty)) = ok z) :
    UScalar.wrapping_mul x y = z ∧ x.val * y.val < 2^ty.numBits := by
  have he := UScalar.mul_equiv x y
  have hop : (x * y : Result (UScalar ty)) = x.mul y := rfl
  rw [hop] at h
  simp only [h] at he
  refine ⟨?_, ?_⟩
  · apply UScalar.eq_of_val_eq
    change (x.bv * y.bv).toNat = z.bv.toNat
    exact congrArg BitVec.toNat he.2.2.symm
  · have hb := he.1
    rw [UScalar.max] at hb
    have hp : 0 < 2^ty.numBits := Nat.pow_pos (by decide)
    omega

def addP {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := x + y
  wrapping := UScalar.wrapping_add x y
  safe := x.val + y.val < 2^ty.numBits
  success v h := (add_success x y v h).symm

def subP {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := x - y
  wrapping := UScalar.wrapping_sub x y
  safe := y.val ≤ x.val
  success v h := (sub_success x y v h).symm

def mulP {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := x * y
  wrapping := UScalar.wrapping_mul x y
  safe := x.val * y.val < 2^ty.numBits
  success v h := (mul_success x y v h).symm

/-- Checked right shift by an unsigned amount (Rust `>>` with overflow checks ON):
fails iff the amount is at least the bit width; the wrapping reading masks nothing
here because `safe` is exactly the in-range condition. -/
def shrP {ty0 ty1 : UScalarTy} (x : UScalar ty0) (s : UScalar ty1) : Primitive (UScalar ty0) where
  checked := x >>> s
  wrapping := ⟨x.bv.ushiftRight s.val⟩
  safe := s.val < ty0.numBits
  success v h := by
    change UScalar.shiftRight x s.val = ok v at h
    unfold UScalar.shiftRight at h
    split at h
    · rename_i hs
      exact ⟨hs, (Result.ok.inj h)⟩
    · cases h

/-! ## Reference bodies (statement-for-statement copies of the gate bodies). -/

def refReduce (x : U64) : Result U32 := do
  let i ← lift (UScalar.cast .U64 P32)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 P32)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= P32
  then x3 - P32
  else ok x3

def refAdd (self : U32) (rhs : U32) : Result U32 := do
  let s ← self + rhs
  if s >= P32
  then let s1 ← s - P32
       ok s1
  else ok s

def refSub (self : U32) (rhs : U32) : Result U32 := do
  let i ← self + P32
  let s ← i - rhs
  if s >= P32
  then let s1 ← s - P32
       ok s1
  else ok s

def refNeg (self : U32) : Result U32 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← P32 - self
       ok i

def refMul (self : U32) (rhs : U32) : Result U32 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← refReduce i2
  ok i3

/-! ## Value-level helpers. -/

theorem max64 : UScalar.max .U64 = 18446744073709551615 := by
  simp only [UScalar.max, UScalarTy.numBits]; decide
theorem max32 : UScalar.max .U32 = 4294967295 := by
  simp only [UScalar.max, UScalarTy.numBits]; decide
theorem ge_P32_iff (s : U32) : (s ≥ P32) ↔ 2147483647 ≤ s.val := Iff.rfl

theorem cast64_val (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  have hx : x.val < 4294967296 := x.bv.isLt
  obtain ⟨y, hy, hv⟩ := WP.spec_imp_exists
    (UScalar.cast_inBounds_spec (src_ty := .U32) .U64 x (by rw [max64]; omega))
  simp only [lift] at hy
  cases hy; exact hv

theorem cast32_val (x : U64) (hx : x.val < 4294967296) : (UScalar.cast .U32 x).val = x.val := by
  obtain ⟨y, hy, hv⟩ := WP.spec_imp_exists
    (UScalar.cast_inBounds_spec (src_ty := .U64) .U32 x (by rw [max32]; omega))
  simp only [lift] at hy
  cases hy; exact hv

theorem and_P_le (x : U64) : (x &&& UScalar.cast .U64 P32).val ≤ 2147483647 := by
  rw [UScalar.val_and, cast64_val, P32_val]
  exact Nat.and_le_right

theorem shr31_val (x : U64) :
    ∃ z, (x >>> 31#u32 : Result U64) = ok z ∧ z.val = x.val / 2147483648 := by
  obtain ⟨z, hz, hv, _⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec x 31#u32 (by decide))
  refine ⟨z, hz, ?_⟩
  rw [hv, Nat.shiftRight_eq_div_pow]; rfl

theorem add_ok {ty : UScalarTy} (x y : UScalar ty) (h : x.val + y.val ≤ UScalar.max ty) :
    ∃ z, (x + y : Result (UScalar ty)) = ok z ∧ z.val = x.val + y.val :=
  WP.spec_imp_exists (UScalar.add_spec h)

theorem sub_ok {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    ∃ z, (x - y : Result (UScalar ty)) = ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv, _⟩ := WP.spec_imp_exists (UScalar.sub_spec h)
  exact ⟨z, hz, hv⟩

theorem mul_ok {ty : UScalarTy} (x y : UScalar ty) (h : x.val * y.val ≤ UScalar.max ty) :
    ∃ z, (x * y : Result (UScalar ty)) = ok z ∧ z.val = x.val * y.val :=
  WP.spec_imp_exists (UScalar.mul_spec h)

/-! ## Checked totality on the domain. -/

/-- TOTAL: every U64 input; canonical output. -/
theorem refReduce_total (x : U64) : ∃ y, refReduce x = ok y ∧ y.val < 2147483647 := by
  have hP := P32_val
  have hx : x.val < 18446744073709551616 := x.bv.isLt
  obtain ⟨i2, h2, v2⟩ := shr31_val x
  have a1 := and_P_le x
  have b1 : (x &&& UScalar.cast .U64 P32).val + i2.val ≤ UScalar.max .U64 := by
    rw [v2, max64]; omega
  obtain ⟨x1, h3, v3⟩ := add_ok _ _ b1
  obtain ⟨i5, h5, v5⟩ := shr31_val x1
  have a4 := and_P_le x1
  have x1b : x1.val < 17179869184 := by rw [v3, v2]; omega
  have i5b : i5.val ≤ 7 := by rw [v5]; omega
  have b2 : (x1 &&& UScalar.cast .U64 P32).val + i5.val ≤ UScalar.max .U64 := by
    rw [max64]; omega
  obtain ⟨x2, h6, v6⟩ := add_ok _ _ b2
  have x2b : x2.val ≤ 2147483647 + 7 := by rw [v6]; omega
  have c := cast32_val x2 (by omega)
  by_cases hge : 2147483647 ≤ (UScalar.cast .U32 x2).val
  · obtain ⟨y, hy, vy⟩ := sub_ok (UScalar.cast .U32 x2) P32 (by rw [P32_val]; exact hge)
    have hc : UScalar.cast .U32 x2 ≥ P32 := (ge_P32_iff _).mpr hge
    refine ⟨y, ?_, by rw [vy, c, P32_val]; omega⟩
    simp only [refReduce, lift, bind_tc_ok, h2, h3, h5, h6, hc, ↓reduceIte, hy]
  · refine ⟨UScalar.cast .U32 x2, ?_, by omega⟩
    have hn : ¬ (UScalar.cast .U32 x2 ≥ P32) := fun h => hge ((ge_P32_iff _).mp h)
    simp only [refReduce, lift, bind_tc_ok, h2, h3, h5, h6, hn, ↓reduceIte]

/-- TOTAL: every pair of stored U32 limbs (the product is widened first). -/
theorem refMul_total (x y : U32) : ∃ z, refMul x y = ok z ∧ z.val < 2147483647 := by
  have hP := P32_val
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have hb : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    rw [cast64_val, cast64_val, max64]; omega
  obtain ⟨p, hp, _⟩ := mul_ok _ _ hb
  obtain ⟨z, hz, vz⟩ := refReduce_total p
  exact ⟨z, by simp only [refMul, lift, bind_tc_ok, hp, hz], vz⟩

/-- PRECONDITION (canonical limbs): both inputs below P. -/
theorem refAdd_total (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, refAdd x y = ok z ∧ z.val < 2147483647 ∧ z.val = (x.val + y.val) % 2147483647 := by
  have hP := P32_val
  obtain ⟨s, hs, vs⟩ := add_ok x y (by rw [max32]; omega)
  by_cases hge : 2147483647 ≤ s.val
  · obtain ⟨r, hr, vr⟩ := sub_ok s P32 (by rw [P32_val]; exact hge)
    have hc : s ≥ P32 := (ge_P32_iff _).mpr hge
    refine ⟨r, ?_, by rw [vr, P32_val]; omega, by rw [vr, P32_val, vs]; omega⟩
    simp only [refAdd, bind_tc_ok, hs, hc, ↓reduceIte, hr]
  · have hn : ¬ (s ≥ P32) := fun h => hge ((ge_P32_iff _).mp h)
    refine ⟨s, ?_, by omega, by rw [vs]; omega⟩
    simp only [refAdd, bind_tc_ok, hs, hn, ↓reduceIte]

/-- PRECONDITION (canonical limbs). -/
theorem refSub_total (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, refSub x y = ok z ∧ z.val < 2147483647 ∧ (z.val + y.val) % 2147483647 = x.val % 2147483647 := by
  have hP := P32_val
  obtain ⟨i, hi, vi⟩ := add_ok x P32 (by rw [P32_val, max32]; omega)
  obtain ⟨s, hs, vs⟩ := sub_ok i y (by rw [vi, P32_val]; omega)
  by_cases hge : 2147483647 ≤ s.val
  · obtain ⟨r, hr, vr⟩ := sub_ok s P32 (by rw [P32_val]; exact hge)
    have hc : s ≥ P32 := (ge_P32_iff _).mpr hge
    refine ⟨r, ?_, by rw [vr, P32_val]; omega, by rw [vr, P32_val, vs, vi, P32_val]; omega⟩
    simp only [refSub, bind_tc_ok, hi, hs, hc, ↓reduceIte, hr]
  · have hn : ¬ (s ≥ P32) := fun h => hge ((ge_P32_iff _).mp h)
    refine ⟨s, ?_, by omega, by rw [vs, vi, P32_val]; omega⟩
    simp only [refSub, bind_tc_ok, hi, hs, hn, ↓reduceIte]

/-- PRECONDITION (input at most P; canonical suffices). -/
theorem refNeg_total (x : U32) (hx : x.val ≤ 2147483647) :
    ∃ z, refNeg x = ok z ∧ z.val < 2147483647 ∧ (z.val + x.val) % 2147483647 = 0 := by
  have hP := P32_val
  by_cases h0 : x = 0#u32
  · subst h0; exact ⟨0#u32, by simp [refNeg], by decide, by decide⟩
  · obtain ⟨r, hr, vr⟩ := sub_ok P32 x (by rw [P32_val]; exact hx)
    have hx0 : x.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    refine ⟨r, ?_, by rw [vr, P32_val]; omega, by rw [vr, P32_val]; omega⟩
    simp only [refNeg, h0, ↓reduceIte, bind_tc_ok, hr]

/-! ## Operational trees: every checked scalar operation of the bodies above is a
`Primitive` step; masks, constants, widening casts and comparisons are the shared pure
runtime operations (as in R22TotalReducerExecution). -/

def finishCode (x3 : U32) : Code U32 :=
  if x3 >= P32 then .step (subP x3 P32) .ret else .ret x3

theorem checked_finishCode (x3 : U32) :
    checked (finishCode x3) = (if x3 >= P32 then x3 - P32 else ok x3) := by
  by_cases hc : x3 ≥ P32
  · simp only [finishCode, hc, ↓reduceIte, checked, subP]
    cases (x3 - P32 : Result U32) <;> rfl
  · simp only [finishCode, hc, ↓reduceIte, checked]

theorem checked_finishCode' (s : U32) :
    checked (finishCode s) = (if s >= P32 then (do let s1 ← s - P32; ok s1) else ok s) := by
  rw [checked_finishCode]
  by_cases hc : s ≥ P32
  · simp only [hc, ↓reduceIte]; cases (s - P32 : Result U32) <;> rfl
  · simp only [hc, ↓reduceIte]

def reduceCode (x : U64) : Code U32 :=
  .step (shrP x 31#u32) (fun i2 =>
  .step (addP (x &&& UScalar.cast .U64 P32) i2) (fun x1 =>
  .step (shrP x1 31#u32) (fun i5 =>
  .step (addP (x1 &&& UScalar.cast .U64 P32) i5) (fun x2 =>
    finishCode (UScalar.cast .U32 x2)))))

theorem checked_reduceCode (x : U64) : checked (reduceCode x) = refReduce x := by
  simp only [reduceCode, refReduce, checked, shrP, addP, lift, bind_tc_ok]
  congr 1; funext a; congr 1; funext b; congr 1; funext c; congr 1; funext d
  exact checked_finishCode _

def addCode (x y : U32) : Code U32 := .step (addP x y) finishCode

theorem checked_addCode (x y : U32) : checked (addCode x y) = refAdd x y := by
  simp only [addCode, refAdd, checked, addP]
  congr 1; funext s
  exact checked_finishCode' s

def subCode (x y : U32) : Code U32 :=
  .step (addP x P32) (fun i => .step (subP i y) finishCode)

theorem checked_subCode (x y : U32) : checked (subCode x y) = refSub x y := by
  simp only [subCode, refSub, checked, addP, subP]
  congr 1; funext i; congr 1; funext s
  exact checked_finishCode' s

def negCode (x : U32) : Code U32 :=
  if x = 0#u32 then .ret 0#u32 else .step (subP P32 x) .ret

theorem checked_negCode (x : U32) : checked (negCode x) = refNeg x := by
  by_cases h0 : x = 0#u32
  · simp only [negCode, refNeg, h0, ↓reduceIte, checked]
  · simp only [negCode, refNeg, h0, ↓reduceIte, checked, subP]

def mulCode (x y : U32) : Code U32 :=
  .step (mulP (UScalar.cast .U64 x) (UScalar.cast .U64 y)) reduceCode

theorem checked_mulCode (x y : U32) : checked (mulCode x y) = refMul x y := by
  simp only [mulCode, refMul, checked, mulP, lift, bind_tc_ok]
  congr 1; funext p
  rw [checked_reduceCode]
  cases refReduce p <;> rfl

/-! ## R22 corollaries (checked = wrapping on the domain, every executed op safe). -/

theorem reduce_R22 (x : U64) : ∃ y, refReduce x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  obtain ⟨y, hy, hc⟩ := refReduce_total x
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_reduceCode x).trans hy)
  exact ⟨y, hy, hc, hs, hw⟩

theorem mul_R22 (x y : U32) : ∃ z, refMul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  obtain ⟨z, hz, hc⟩ := refMul_total x y
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_mulCode x y).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

theorem add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) : ∃ z, refAdd x y = ok z ∧
    z.val < 2147483647 ∧ NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  obtain ⟨z, hz, hc, _⟩ := refAdd_total x y hx hy
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_addCode x y).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

theorem sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) : ∃ z, refSub x y = ok z ∧
    z.val < 2147483647 ∧ NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  obtain ⟨z, hz, hc, _⟩ := refSub_total x y hx hy
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_subCode x y).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

theorem neg_R22 (x : U32) (hx : x.val ≤ 2147483647) : ∃ z, refNeg x = ok z ∧
    z.val < 2147483647 ∧ NoOverflow (negCode x) ∧ wrapping (negCode x) = ok z := by
  obtain ⟨z, hz, hc, _⟩ := refNeg_total x hx
  obtain ⟨hs, hw⟩ := success_noOverflow_agrees _ _ ((checked_negCode x).trans hz)
  exact ⟨z, hz, hc, hs, hw⟩

/-- The domain is necessary (2021 R22TotalDomainObstructions, re-proved on the reference):
the non-canonical stored pair (2^32-1, 1) makes the checked add fail, so no
accepted-run-only argument can stand in for the caller's canonicality. -/
theorem add_noncanonical_fails (z : U32) : refAdd 4294967295#u32 1#u32 ≠ ok z := by
  intro h
  unfold refAdd at h
  cases hc : (4294967295#u32 + 1#u32 : Result U32) with
  | ok s => have hb := (add_success _ _ _ hc).2; exact absurd hb (by decide)
  | fail e => rw [hc] at h; cases h
  | div => rw [hc] at h; cases h

#print axioms refReduce_total
#print axioms refMul_total
#print axioms refAdd_total
#print axioms refSub_total
#print axioms refNeg_total
#print axioms checked_finishCode
#print axioms checked_reduceCode
#print axioms checked_addCode
#print axioms checked_subCode
#print axioms checked_negCode
#print axioms checked_mulCode
#print axioms reduce_R22
#print axioms mul_R22
#print axioms add_R22
#print axioms sub_R22
#print axioms neg_R22
#print axioms add_noncanonical_fails
end AspisR1.NPH_R22FieldRef
