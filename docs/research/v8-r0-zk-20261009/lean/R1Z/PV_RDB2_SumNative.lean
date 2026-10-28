import R1Z.PV_RDB2_SumFold
set_option autoImplicit false
noncomputable section
namespace PV_B1_SumNative
open Aeneas Aeneas.Std Result PV_B1_230 PV_B1_SumControl

def limbAdd (a b : U32) : U32 :=
  let x := U32.wrapping_add a b
  let mask := U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 (x >= aspis_core.field.P))
  U32.wrapping_sub x (aspis_core.field.P &&& mask)

def add (a b : Q) : Q :=
  { c0 := { a := limbAdd a.c0.a b.c0.a, b := limbAdd a.c0.b b.c0.b },
    c1 := { a := limbAdd a.c1.a b.c1.a, b := limbAdd a.c1.b b.c1.b } }

theorem limb_source (a b : U32) :
    aspis_core.field.M31.add a b = ok (limbAdd a b) := by
  simp only [aspis_core.field.M31.add,aspis_core.field.ct.add,
    aspis_core.field.ct.subtract_p,lift,bind_tc_ok,limbAdd,
    core.num.U32.wrapping_add,core.num.U32.wrapping_sub,U32.wrapping_add,U32.wrapping_sub] <;> rfl

theorem add_source (a b : Q) :
    aspis_core.field.QM31.add a b = ok (add a b) := by
  simp only [aspis_core.field.QM31.add,aspis_core.field.CM31.add,
    limb_source,bind_tc_ok,add]

theorem fold_source (xs : List Q) (sum : Q) :
    PV_B1_SumFold.fold xs sum = ok (xs.foldl add sum) := by
  induction xs generalizing sum with
  | nil => rfl
  | cons x xs ih =>
    simp only [PV_B1_SumFold.fold,add_source,bind_tc_ok,List.foldl_cons,ih]

theorem op230_source (h1 : Slice Q) :
    state_only_copy_helper_sum h1 =
      ok (if Slice.len h1 = TRACE_ROWS then
        some (h1.val.foldl add aspis_core.field.QM31.ZERO) else none) := by
  rw [PV_B1_SumFold.op230_source]
  split
  · simp only [fold_source,bind_tc_ok]
  · rfl
#print axioms limb_source
#print axioms add_source
#print axioms fold_source
#print axioms op230_source
end PV_B1_SumNative
