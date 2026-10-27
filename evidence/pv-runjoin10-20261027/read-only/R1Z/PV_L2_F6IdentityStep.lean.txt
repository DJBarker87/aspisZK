import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6IdentityRow

set_option autoImplicit false
namespace R1Z.PV_L2_F6IdentityStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) (ok1 : Bool) (i : Usize) : Result (Bool × Usize) := do
  let b ← id_row_ok c co i w
  let i1 ← i + 1#usize
  ok (ok1 && b,i1)
def recorded 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) (ok1 : Bool) (i : Usize) : Recorded (Bool × Usize) := do
  let b ← PV_L2_F6IdentityRow.recorded c co i w
  let i1 ← operation (.add i.val (1#usize).val) (i + 1#usize)
  operation (.guard 20 0 0 (ok1 && b)) (ok (ok1 && b,i1))
theorem recorded_erases 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) (ok1 : Bool) (i : Usize) :
    (recorded c co w ok1 i).value = step c co w ok1 i := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    PV_L2_F6IdentityRow.erases,PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) (ok1 : Bool) (i : Usize) :
    id_ok_loop c co w ok1 i = if i<w then (do
      let (flag1,index1) ← step c co w ok1 i
      id_ok_loop c co w flag1 index1) else ok ok1 := by
  rw [id_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) (ok1 : Bool) (i : Usize) (after : Bool × Usize)
    (success : step c co w ok1 i = ok after) : after.2.val=i.val+1 := by
  unfold step at success
  obtain ⟨b,hb,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hi1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6IdentityStep
