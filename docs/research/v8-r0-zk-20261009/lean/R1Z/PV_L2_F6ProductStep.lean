import R1Z.PV_L2_F6Dot
import R1Z.PV_L2_RecordBind

/-! One actual extracted product-row iteration, including concrete dot calls,
checked arithmetic, comparison operands and every nested error prefix. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6ProductStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_RecordBind

def step (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) (flag : Bool) (j : Usize) : Result (Bool × Usize) := do
  let i1 ← i*len
  let i2 ← ao+i1
  let i3 ← bo+j
  let i4 ← R1CertCheck.dot a i2 1#usize b i3 nj len
  let i5 ← i*nj
  let i6 ← co+i5
  let i7 ← i6+j
  let i8 ← Slice.index_usize c i7
  let i9 ← lift (UScalar.cast .U64 i8)
  let j1 ← j+1#usize
  ok (flag && (i4=i9),j1)

def recorded (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) (flag : Bool) (j : Usize) : Recorded (Bool × Usize) := do
  let i1 ← operation (.mul i.val len.val) (i*len)
  let i2 ← operation (.add ao.val i1.val) (ao+i1)
  let i3 ← operation (.add bo.val j.val) (bo+j)
  let i4 ← PV_L2_F6Dot.dot a i2 1#usize b i3 nj len
  let i5 ← operation (.mul i.val nj.val) (i*nj)
  let i6 ← operation (.add co.val i5.val) (co+i5)
  let i7 ← operation (.add i6.val j.val) (i6+j)
  let i8 ← operation (.index 2 i7.val) (Slice.index_usize c i7)
  let i9 := UScalar.cast .U64 i8
  let j1 ← operation (.add j.val 1) (j+1#usize)
  operation (.guard 5 i4.val i9.val (i4=i9)) (ok (flag && (i4=i9),j1))

theorem recorded_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) (flag : Bool) (j : Usize) :
    (recorded a ao b bo c co i nj len flag j).value = step a ao b bo c co i nj len flag j := by
  simp only [recorded,step,operation_bind_value,erase_bind,PV_L2_F6Dot.dot_erases,
    operation_value,lift,bind_tc_ok]

theorem unroll (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) (flag : Bool) (j : Usize) :
    prod_row_ok_loop a ao b bo c co i nj len flag j =
      if j<nj then (do
        let (flag1,j1) ← step a ao b bo c co i nj len flag j
        prod_row_ok_loop a ao b bo c co i nj len flag1 j1) else ok flag := by
  rw [prod_row_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) (flag : Bool) (j : Usize) (after : Bool × Usize)
    (success : step a ao b bo c co i nj len flag j = ok after) : after.2.val=j.val+1 := by
  unfold step at success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨i3,hi3,success⟩ := bind_eq_ok success
  obtain ⟨i4,hi4,success⟩ := bind_eq_ok success
  obtain ⟨i5,hi5,success⟩ := bind_eq_ok success
  obtain ⟨i6,hi6,success⟩ := bind_eq_ok success
  obtain ⟨i7,hi7,success⟩ := bind_eq_ok success
  obtain ⟨i8,hi8,success⟩ := bind_eq_ok success
  obtain ⟨i9,hi9,success⟩ := bind_eq_ok success
  obtain ⟨j1,hj1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hj1

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6ProductStep
