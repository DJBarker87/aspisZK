import R1Z.PV_L2_F6ProductRow
import R1Z.PV_L2_RecordBind
set_option autoImplicit false
namespace R1Z.PV_L2_F6ProductOuterStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_RecordBind

def step (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co nj len : Usize) (flag : Bool) (i : Usize) : Result (Bool × Usize) := do
  let result ← prod_row_ok a ao b bo c co i nj len
  let i1 ← i+1#usize
  ok (flag && result,i1)

def recorded (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co nj len : Usize) (flag : Bool) (i : Usize) : Recorded (Bool × Usize) := do
  let result ← PV_L2_F6ProductRow.loop a ao b bo c co i nj len nj.val true 0#usize
  let i1 ← operation (.add i.val 1) (i+1#usize)
  PV_L2_Record.pure (flag && result,i1)

theorem recorded_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co nj len : Usize) (flag : Bool) (i : Usize) :
    (recorded a ao b bo c co nj len flag i).value = step a ao b bo c co nj len flag i := by
  simp only [recorded,step,erase_bind,PV_L2_F6ProductRow.row_erases,
    operation_value,pure_value]

theorem unroll (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) (flag : Bool) (i : Usize) :
    prod_ok_loop a ao b bo c co ni nj len flag i =
      if i<ni then (do
        let (flag1,i1) ← step a ao b bo c co nj len flag i
        prod_ok_loop a ao b bo c co ni nj len flag1 i1) else ok flag := by
  rw [prod_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co nj len : Usize) (flag : Bool) (i : Usize) (after : Bool × Usize)
    (success : step a ao b bo c co nj len flag i = ok after) : after.2.val=i.val+1 := by
  unfold step at success
  obtain ⟨result,hr,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hi1

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6ProductOuterStep
