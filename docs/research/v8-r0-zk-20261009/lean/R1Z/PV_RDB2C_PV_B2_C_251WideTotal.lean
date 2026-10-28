import R1Z.PV_RDB2C_PV_B2_C_251FieldTotal
set_option autoImplicit false
namespace PV_B2_C_251WideValue
open Aeneas Aeneas.Std PV_B2_251c1
def aspis_core.field.wide_exact.WideExact.add
  (self : PV_B2_251c1.aspis_core.field.wide_exact.WideExact)
  (rhs : PV_B2_251c1.aspis_core.field.wide_exact.WideExact) :
  PV_B2_251c1.aspis_core.field.wide_exact.WideExact
  :=
  let q := PV_B2_C_251FieldValue.aspis_core.field.QM31.add self.c0 rhs.c0
  let q1 := PV_B2_C_251FieldValue.aspis_core.field.QM31.add self.c1 rhs.c1
  { c0 := q, c1 := q1 }
end PV_B2_C_251WideValue
namespace PV_B2_C_251WideTotal
open Aeneas Aeneas.Std Result
theorem WideExact_add (self rhs : PV_B2_251c1.aspis_core.field.wide_exact.WideExact) :
 PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add self rhs = ok (PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.add self rhs) := by
 unfold PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.add
 simp only [PV_B2_C_251FieldTotal.QM31_add,PV_B2_C_251FieldTotal.QM31_sub,PV_B2_C_251FieldTotal.QM31_mul,PV_B2_C_251FieldTotal.mul_by_r,bind_tc_ok]
#print axioms WideExact_add
end PV_B2_C_251WideTotal
namespace PV_B2_C_251WideValue
open Aeneas Aeneas.Std PV_B2_251c1
def aspis_core.field.wide_exact.mul_u
  (value : PV_B2_C_251FieldValue.aspis_core.field.QM31) : PV_B2_C_251FieldValue.aspis_core.field.QM31 :=
  let c := PV_B2_C_251FieldValue.aspis_core.field.mul_by_r value.c1
  { c0 := c, c1 := value.c0 }
end PV_B2_C_251WideValue
namespace PV_B2_C_251WideTotal
open Aeneas Aeneas.Std Result
theorem mul_u (value : PV_B2_251c1.aspis_core.field.QM31) :
 PV_B2_251c1.aspis_core.field.wide_exact.mul_u value = ok (PV_B2_C_251WideValue.aspis_core.field.wide_exact.mul_u value) := by
 unfold PV_B2_251c1.aspis_core.field.wide_exact.mul_u PV_B2_C_251WideValue.aspis_core.field.wide_exact.mul_u
 simp only [PV_B2_C_251FieldTotal.QM31_add,PV_B2_C_251FieldTotal.QM31_sub,PV_B2_C_251FieldTotal.QM31_mul,PV_B2_C_251FieldTotal.mul_by_r,bind_tc_ok,PV_B2_C_251WideTotal.WideExact_add]
#print axioms mul_u
end PV_B2_C_251WideTotal
namespace PV_B2_C_251WideValue
open Aeneas Aeneas.Std PV_B2_251c1
def aspis_core.field.wide_exact.WideExact.mul
  (self : PV_B2_251c1.aspis_core.field.wide_exact.WideExact)
  (rhs : PV_B2_251c1.aspis_core.field.wide_exact.WideExact) :
  PV_B2_251c1.aspis_core.field.wide_exact.WideExact
  :=
  let ac := PV_B2_C_251FieldValue.aspis_core.field.QM31.mul self.c0 rhs.c0
  let bd := PV_B2_C_251FieldValue.aspis_core.field.QM31.mul self.c1 rhs.c1
  let q := PV_B2_C_251FieldValue.aspis_core.field.QM31.add self.c0 self.c1
  let q1 := PV_B2_C_251FieldValue.aspis_core.field.QM31.add rhs.c0 rhs.c1
  let cross := PV_B2_C_251FieldValue.aspis_core.field.QM31.mul q q1
  let q2 := PV_B2_C_251WideValue.aspis_core.field.wide_exact.mul_u bd
  let q3 := PV_B2_C_251FieldValue.aspis_core.field.QM31.add ac q2
  let q4 := PV_B2_C_251FieldValue.aspis_core.field.QM31.sub cross ac
  let q5 := PV_B2_C_251FieldValue.aspis_core.field.QM31.sub q4 bd
  { c0 := q3, c1 := q5 }
end PV_B2_C_251WideValue
namespace PV_B2_C_251WideTotal
open Aeneas Aeneas.Std Result
theorem WideExact_mul (self rhs : PV_B2_251c1.aspis_core.field.wide_exact.WideExact) :
 PV_B2_251c1.aspis_core.field.wide_exact.WideExact.mul self rhs = ok (PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.mul self rhs) := by
 unfold PV_B2_251c1.aspis_core.field.wide_exact.WideExact.mul PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.mul
 simp only [PV_B2_C_251FieldTotal.QM31_add,PV_B2_C_251FieldTotal.QM31_sub,PV_B2_C_251FieldTotal.QM31_mul,PV_B2_C_251FieldTotal.mul_by_r,bind_tc_ok,PV_B2_C_251WideTotal.WideExact_add,PV_B2_C_251WideTotal.mul_u]
#print axioms WideExact_mul
end PV_B2_C_251WideTotal
