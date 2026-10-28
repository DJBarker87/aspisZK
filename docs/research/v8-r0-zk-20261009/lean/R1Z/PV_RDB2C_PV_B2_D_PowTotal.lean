import R1Z.PV_RDB2C_PV_B2_D_RawHelpersTotal
set_option autoImplicit false
namespace PV_B2_D_PowTotal
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1 PV_B2_C_ArrayTotal
abbrev Q := aspis_core.field.QM31

theorem csquare (c : aspis_core.field.CM31) : Total (aspis_core.field.CM31.square c) := by
  unfold aspis_core.field.CM31.square
  simp only [PV_B2_C_251FieldTotal.M31_add,PV_B2_C_251FieldTotal.M31_sub,
    PV_B2_C_251FieldTotal.M31_mul,PV_B2_C_251FieldTotal.M31_double,bind_tc_ok]
  exact ⟨_,rfl⟩
theorem cdouble (c : aspis_core.field.CM31) : Total (aspis_core.field.CM31.double c) := by
  unfold aspis_core.field.CM31.double
  simp only [PV_B2_C_251FieldTotal.CM31_add,PV_B2_C_251FieldTotal.M31_double,bind_tc_ok]
  exact ⟨_,rfl⟩
theorem square (q : Q) : Total (aspis_core.field.QM31.square q) := by
  unfold aspis_core.field.QM31.square
  simp only [PV_B2_C_251FieldTotal.mul_by_r,PV_B2_C_251FieldTotal.CM31_add,
    PV_B2_C_251FieldTotal.CM31_mul]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact csquare _
    | exact cdouble _
    | apply PV_B2_C_ArrayTotal.bind
    | intro x

theorem body (e : U64) (b a : Q) (he : e > 0#u64) :
    ∃ b1 a1, aspis_core.field.QM31.pow_loop.body e b a =
      ok (cont (U64.wrapping_shr e 1#u32,b1,a1)) := by
  obtain ⟨b1,hb⟩ := square b
  unfold aspis_core.field.QM31.pow_loop.body
  simp only [he,if_pos,lift,bind_tc_ok]
  split
  · simp only [PV_B2_C_251FieldTotal.QM31_mul,bind_tc_ok,hb]
    exact ⟨_,_,rfl⟩
  · simp only [bind_tc_ok,hb]
    exact ⟨_,_,rfl⟩

theorem shift_lt (e : U64) (he : e > 0#u64) :
    (U64.wrapping_shr e 1#u32).val < e.val := by
  simp only [U64.wrapping_shr,UScalar.wrapping_shr,UScalar.val,
    U32.ofNat_bv,UScalarTy.numBits,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  change e.val / 2 < e.val
  apply Nat.div_lt_self
  · change 0 < e.val at he
    exact he
  · decide

theorem loop_total (e : U64) (b a : Q) : Total (aspis_core.field.QM31.pow_loop e b a) := by
  suffices ∀ n (e : U64) (b a : Q), e.val = n → Total (aspis_core.field.QM31.pow_loop e b a) from
    this e.val e b a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro e b a hn
    by_cases he : e > 0#u64
    · obtain ⟨b1,a1,hbody⟩ := body e b a he
      obtain ⟨r,hr⟩ := ih (U64.wrapping_shr e 1#u32).val (by simpa only [← hn] using shift_lt e he)
        (U64.wrapping_shr e 1#u32) b1 a1 rfl
      refine ⟨r,?_⟩
      unfold aspis_core.field.QM31.pow_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [hbody,bind_tc_ok]
      exact hr
    · refine ⟨a,?_⟩
      unfold aspis_core.field.QM31.pow_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [aspis_core.field.QM31.pow_loop.body,he,if_neg,if_false,bind_tc_ok]

theorem source (q : Q) (e : U64) : Total (aspis_core.field.QM31.pow q e) :=
  loop_total e q aspis_core.field.QM31.ONE
#print axioms csquare
#print axioms cdouble
#print axioms square
#print axioms body
#print axioms shift_lt
#print axioms loop_total
#print axioms source
end PV_B2_D_PowTotal
