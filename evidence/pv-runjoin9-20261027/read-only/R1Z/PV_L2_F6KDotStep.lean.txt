import R1Z.PV_L2_Record
import R1Z.CertCheckDot

/-! Exact operational one-iteration factorization of the extracted c3 dot
checker. No success is assumed for arithmetic or indexing; the increment
lemma is conditional only on that concrete step returning successfully. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6KDotStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck
open R1Z.PV_L2_Record

/-- Exact checked operations of kdot_loop, in their extracted order. -/
def step (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co : Usize) (acc : U64) (p : Usize) : Result (U64 × Usize) := do
  let i1 ← io + p
  let i2 ← Slice.index_usize idx i1
  let t ← lift (UScalar.cast .Usize i2)
  let i3 ← t * st
  let i4 ← i3 + i
  let i5 ← Slice.index_usize m i4
  let x ← lift (UScalar.cast .U64 i5)
  let i6 ← co + p
  let i7 ← Slice.index_usize c i6
  let y ← lift (UScalar.cast .U64 i7)
  let i8 ← x * y
  let i9 ← i8 % P
  let acc1 ← acc + i9
  let p1 ← p + 1#usize
  ok (acc1,p1)

def recorded (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co : Usize) (acc : U64) (p : Usize) : Recorded (U64 × Usize) := do
  let i1 ← operation (.add io.val p.val) (io + p)
  let i2 ← operation (.index 0 i1.val) (Slice.index_usize idx i1)
  let t := UScalar.cast .Usize i2
  let i3 ← operation (.mul t.val st.val) (t * st)
  let i4 ← operation (.add i3.val i.val) (i3 + i)
  let i5 ← operation (.index 1 i4.val) (Slice.index_usize m i4)
  let x := UScalar.cast .U64 i5
  let i6 ← operation (.add co.val p.val) (co + p)
  let i7 ← operation (.index 2 i6.val) (Slice.index_usize c i6)
  let y := UScalar.cast .U64 i7
  let i8 ← operation (.mul x.val y.val) (x * y)
  let i9 ← operation (.rem i8.val P.val) (i8 % P)
  let acc1 ← operation (.add acc.val i9.val) (acc + i9)
  let p1 ← operation (.add p.val 1) (p + 1#usize)
  PV_L2_Record.pure (acc1,p1)

theorem recorded_erases (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co : Usize) (acc : U64) (p : Usize) :
    (recorded m st i idx io c co acc p).value = step m st i idx io c co acc p := by
  simp only [recorded,operation_bind_value,pure_value,step,lift,bind_tc_ok]

theorem unroll (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co n : Usize) (acc : U64) (p : Usize) :
    kdot_loop m st i idx io c co n acc p =
      if p < n then (do
        let (acc1,p1) ← step m st i idx io c co acc p
        kdot_loop m st i idx io c co n acc1 p1) else ok acc := by
  rw [kdot_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co : Usize) (acc : U64) (p : Usize) (after : U64 × Usize)
    (success : step m st i idx io c co acc p = ok after) : after.2.val = p.val+1 := by
  unfold step at success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨t,ht,success⟩ := bind_eq_ok success
  obtain ⟨i3,hi3,success⟩ := bind_eq_ok success
  obtain ⟨i4,hi4,success⟩ := bind_eq_ok success
  obtain ⟨i5,hi5,success⟩ := bind_eq_ok success
  obtain ⟨x,hx,success⟩ := bind_eq_ok success
  obtain ⟨i6,hi6,success⟩ := bind_eq_ok success
  obtain ⟨i7,hi7,success⟩ := bind_eq_ok success
  obtain ⟨y,hy,success⟩ := bind_eq_ok success
  obtain ⟨i8,hi8,success⟩ := bind_eq_ok success
  obtain ⟨i9,hi9,success⟩ := bind_eq_ok success
  obtain ⟨acc1,hacc1,success⟩ := bind_eq_ok success
  obtain ⟨p1,hp1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [← he]
  have hv := add_ok hp1
  simpa only [show (1#usize).val=1 from rfl] using hv

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6KDotStep
