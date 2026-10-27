import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6Callers
import R1Z.PV_L2_F6Identity

set_option autoImplicit false
namespace R1Z.PV_L2_F6LiftsStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) (ok1 : Bool) (l : Usize) : Result (Bool × Usize) := do
  let i ← Slice.index_usize lw l
  let w ← lift (UScalar.cast .Usize i)
  let i1 ← Slice.index_usize loff l
  let off ← lift (UScalar.cast .Usize i1)
  let b0 ← prod_ok o off u off id off w w w
  let b1 ← id_ok id off w
  let l1 ← l + 1#usize
  ok ((ok1 && b0) && b1,l1)
def recorded 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) (ok1 : Bool) (l : Usize) : Recorded (Bool × Usize) := do
  let i ← operation (.index 3 l.val) (Slice.index_usize lw l)
  let w := UScalar.cast .Usize i
  let i1 ← operation (.index 4 l.val) (Slice.index_usize loff l)
  let off := UScalar.cast .Usize i1
  let b0 ← PV_L2_F6Callers.product o off u off id off w w w
  let b1 ← PV_L2_F6Identity.recorded id off w
  let l1 ← operation (.add l.val (1#usize).val) (l + 1#usize)
  operation (.guard 23 0 0 ((ok1 && b0) && b1)) (ok ((ok1 && b0) && b1,l1))
theorem recorded_erases 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) (ok1 : Bool) (l : Usize) :
    (recorded o u id lw loff nl ok1 l).value = step o u id lw loff nl ok1 l := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    PV_L2_F6Callers.product_erases,PV_L2_F6Identity.erases,PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) (ok1 : Bool) (l : Usize) :
    lifts_ok_loop o u id lw loff nl ok1 l = if l<nl then (do
      let (flag1,index1) ← step o u id lw loff nl ok1 l
      lifts_ok_loop o u id lw loff nl flag1 index1) else ok ok1 := by
  rw [lifts_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) (ok1 : Bool) (l : Usize) (after : Bool × Usize)
    (success : step o u id lw loff nl ok1 l = ok after) : after.2.val=l.val+1 := by
  unfold step at success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨w,hw,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨off,hoff,success⟩ := bind_eq_ok success
  obtain ⟨b0,hb0,success⟩ := bind_eq_ok success
  obtain ⟨b1,hb1,success⟩ := bind_eq_ok success
  obtain ⟨l1,hl1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hl1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6LiftsStep
