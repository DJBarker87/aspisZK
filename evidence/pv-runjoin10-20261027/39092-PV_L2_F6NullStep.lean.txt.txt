import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6NullRow

set_option autoImplicit false
namespace R1Z.PV_L2_F6NullStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) (ok1 : Bool) (f : Usize) : Result (Bool × Usize) := do
  let i ← r + f
  let i1 ← Slice.index_usize lst i
  let ff ← lift (UScalar.cast .Usize i1)
  let b ← nvec_row_ok nm e n tag r f ff
  let f1 ← f + 1#usize
  ok (ok1 && b,f1)
def recorded 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) (ok1 : Bool) (f : Usize) : Recorded (Bool × Usize) := do
  let i ← operation (.add r.val f.val) (r + f)
  let i1 ← operation (.index 3 i.val) (Slice.index_usize lst i)
  let ff := UScalar.cast .Usize i1
  let b ← PV_L2_F6NullRow.recorded nm e n tag r f ff
  let f1 ← operation (.add f.val (1#usize).val) (f + 1#usize)
  operation (.guard 22 0 0 (ok1 && b)) (ok (ok1 && b,f1))
theorem recorded_erases 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) (ok1 : Bool) (f : Usize) :
    (recorded nm e n lst tag r k ok1 f).value = step nm e n lst tag r k ok1 f := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    PV_L2_F6NullRow.erases,PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) (ok1 : Bool) (f : Usize) :
    nvec_ok_loop nm e n lst tag r k ok1 f = if f<k then (do
      let (flag1,index1) ← step nm e n lst tag r k ok1 f
      nvec_ok_loop nm e n lst tag r k flag1 index1) else ok ok1 := by
  rw [nvec_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) (ok1 : Bool) (f : Usize) (after : Bool × Usize)
    (success : step nm e n lst tag r k ok1 f = ok after) : after.2.val=f.val+1 := by
  unfold step at success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨ff,hff,success⟩ := bind_eq_ok success
  obtain ⟨b,hb,success⟩ := bind_eq_ok success
  obtain ⟨f1,hf1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hf1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6NullStep
