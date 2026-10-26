import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6EchelonRow

set_option autoImplicit false
namespace R1Z.PV_L2_F6EchelonStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) (ok1 : Bool) (a : Usize) : Result (Bool × Usize) := do
  let b ← ech_row_ok e n lst a r
  let a1 ← a + 1#usize
  ok (ok1 && b,a1)
def recorded 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) (ok1 : Bool) (a : Usize) : Recorded (Bool × Usize) := do
  let b ← PV_L2_F6EchelonRow.recorded e n lst a r
  let a1 ← operation (.add a.val (1#usize).val) (a + 1#usize)
  operation (.guard 21 0 0 (ok1 && b)) (ok (ok1 && b,a1))
theorem recorded_erases 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) (ok1 : Bool) (a : Usize) :
    (recorded e n lst r ok1 a).value = step e n lst r ok1 a := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    PV_L2_F6EchelonRow.erases,PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) (ok1 : Bool) (a : Usize) :
    ech_ok_loop e n lst r ok1 a = if a<r then (do
      let (flag1,index1) ← step e n lst r ok1 a
      ech_ok_loop e n lst r flag1 index1) else ok ok1 := by
  rw [ech_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) (ok1 : Bool) (a : Usize) (after : Bool × Usize)
    (success : step e n lst r ok1 a = ok after) : after.2.val=a.val+1 := by
  unfold step at success
  obtain ⟨b,hb,success⟩ := bind_eq_ok success
  obtain ⟨a1,ha1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok ha1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6EchelonStep
