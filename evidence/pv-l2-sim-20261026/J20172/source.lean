import R1Z.PV_L2_F6KDot
import R1Z.PV_L2_RecordBind

/-! One extracted image-check row with the concrete recorded kdot, not an
abstract arithmetic callback. Failures retain their nested call prefix. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6ImageStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_RecordBind

def step (m : Slice U32) (st j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (flag : Bool) (i : Usize) : Result (Bool × Usize) := do
  let i1 ← j * st
  let i2 ← i1 + i
  let i3 ← Slice.index_usize m i2
  let i4 ← lift (UScalar.cast .U64 i3)
  let i5 ← kdot m st i idx io c co s
  let i6 ← i4 + i5
  let v ← i6 % P
  let i7 ← i * ts
  let i8 ← to1 + i7
  let i9 ← Slice.index_usize tgt i8
  let i10 ← lift (UScalar.cast .U64 i9)
  let i11 ← i + 1#usize
  ok (flag && (v=i10),i11)

def recorded (m : Slice U32) (st j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (flag : Bool) (i : Usize) : Recorded (Bool × Usize) := do
  let i1 ← operation (.mul j.val st.val) (j*st)
  let i2 ← operation (.add i1.val i.val) (i1+i)
  let i3 ← operation (.index 0 i2.val) (Slice.index_usize m i2)
  let i4 := UScalar.cast .U64 i3
  let i5 ← PV_L2_F6KDot.kdot m st i idx io c co s
  let i6 ← operation (.add i4.val i5.val) (i4+i5)
  let v ← operation (.rem i6.val P.val) (i6%P)
  let i7 ← operation (.mul i.val ts.val) (i*ts)
  let i8 ← operation (.add to1.val i7.val) (to1+i7)
  let i9 ← operation (.index 1 i8.val) (Slice.index_usize tgt i8)
  let i10 := UScalar.cast .U64 i9
  let i11 ← operation (.add i.val 1) (i+1#usize)
  operation (.guard 4 v.val i10.val (v=i10)) (ok (flag && (v=i10),i11))

theorem recorded_erases (m : Slice U32) (st j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (flag : Bool) (i : Usize) :
    (recorded m st j idx io c co s tgt to1 ts flag i).value =
      step m st j idx io c co s tgt to1 ts flag i := by
  simp only [recorded,step,operation_bind_value,erase_bind,PV_L2_F6KDot.kdot_erases,
    operation_value,lift,bind_tc_ok]

theorem unroll (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (flag : Bool) (i : Usize) :
    kimg_ok_loop m st nrows j idx io c co s tgt to1 ts flag i =
      if i<nrows then (do
        let (flag1,i1) ← step m st j idx io c co s tgt to1 ts flag i
        kimg_ok_loop m st nrows j idx io c co s tgt to1 ts flag1 i1) else ok flag := by
  rw [kimg_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (m : Slice U32) (st j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (flag : Bool) (i : Usize) (after : Bool × Usize)
    (success : step m st j idx io c co s tgt to1 ts flag i = ok after) : after.2.val=i.val+1 := by
  unfold step at success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨i3,hi3,success⟩ := bind_eq_ok success
  obtain ⟨i4,hi4,success⟩ := bind_eq_ok success
  obtain ⟨i5,hi5,success⟩ := bind_eq_ok success
  obtain ⟨i6,hi6,success⟩ := bind_eq_ok success
  obtain ⟨v,hv,success⟩ := bind_eq_ok success
  obtain ⟨i7,hi7,success⟩ := bind_eq_ok success
  obtain ⟨i8,hi8,success⟩ := bind_eq_ok success
  obtain ⟨i9,hi9,success⟩ := bind_eq_ok success
  obtain ⟨i10,hi10,success⟩ := bind_eq_ok success
  obtain ⟨i11,hi11,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hi11

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6ImageStep
