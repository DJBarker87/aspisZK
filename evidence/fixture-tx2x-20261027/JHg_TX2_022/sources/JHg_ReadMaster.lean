import JHg_DataMaster
import JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_ReadMaster
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataMaster.value JHg_FieldRead.segment
theorem length : JHg_DataMaster.value.val.length=384 := by unfold JHg_DataMaster.value;exact JHg_DataMaster.length
#print axioms length
theorem magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=0#usize,«end»:=4#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 0 4) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 0#usize 4#usize (by decide)
    (by rw [length];decide)
  simpa only [show (0#usize).val=0 from rfl,
    show (4#usize).val=4 from rfl,Nat.reduceSub] using call
#print axioms magic
theorem version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=4#usize,«end»:=5#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 4 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 4#usize 5#usize (by decide)
    (by rw [length];decide)
  simpa only [show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,Nat.reduceSub] using call
#print axioms version
theorem lanes : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=5#usize,«end»:=6#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 5 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 5#usize 6#usize (by decide)
    (by rw [length];decide)
  simpa only [show (5#usize).val=5 from rfl,
    show (6#usize).val=6 from rfl,Nat.reduceSub] using call
#print axioms lanes
theorem encoding : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=6#usize,«end»:=7#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 6 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 6#usize 7#usize (by decide)
    (by rw [length];decide)
  simpa only [show (6#usize).val=6 from rfl,
    show (7#usize).val=7 from rfl,Nat.reduceSub] using call
#print axioms encoding
theorem bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=7#usize,«end»:=8#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 7 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 7#usize 8#usize (by decide)
    (by rw [length];decide)
  simpa only [show (7#usize).val=7 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub] using call
#print axioms bump
theorem format : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=8#usize,«end»:=40#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 8 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 8#usize 40#usize (by decide)
    (by rw [length];decide)
  simpa only [show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,Nat.reduceSub] using call
#print axioms format
theorem next_checkpoint : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=40#usize,«end»:=48#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 40 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 40#usize 48#usize (by decide)
    (by rw [length];decide)
  simpa only [show (40#usize).val=40 from rfl,
    show (48#usize).val=48 from rfl,Nat.reduceSub] using call
#print axioms next_checkpoint
theorem lane_mask : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=48#usize,«end»:=49#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 48 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 48#usize 49#usize (by decide)
    (by rw [length];decide)
  simpa only [show (48#usize).val=48 from rfl,
    show (49#usize).val=49 from rfl,Nat.reduceSub] using call
#print axioms lane_mask
theorem has_checkpoint : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=49#usize,«end»:=50#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 49 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 49#usize 50#usize (by decide)
    (by rw [length];decide)
  simpa only [show (49#usize).val=49 from rfl,
    show (50#usize).val=50 from rfl,Nat.reduceSub] using call
#print axioms has_checkpoint
theorem reserved0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=50#usize,«end»:=64#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 50 14) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 50#usize 64#usize (by decide)
    (by rw [length];decide)
  simpa only [show (50#usize).val=50 from rfl,
    show (64#usize).val=64 from rfl,Nat.reduceSub] using call
#print axioms reserved0
theorem identity_magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=64#usize,«end»:=68#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 64 4) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 64#usize 68#usize (by decide)
    (by rw [length];decide)
  simpa only [show (64#usize).val=64 from rfl,
    show (68#usize).val=68 from rfl,Nat.reduceSub] using call
#print axioms identity_magic
theorem identity_version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=68#usize,«end»:=69#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 68 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 68#usize 69#usize (by decide)
    (by rw [length];decide)
  simpa only [show (68#usize).val=68 from rfl,
    show (69#usize).val=69 from rfl,Nat.reduceSub] using call
#print axioms identity_version
theorem identity_reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=69#usize,«end»:=72#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 69 3) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 69#usize 72#usize (by decide)
    (by rw [length];decide)
  simpa only [show (69#usize).val=69 from rfl,
    show (72#usize).val=72 from rfl,Nat.reduceSub] using call
#print axioms identity_reserved
theorem pool : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=72#usize,«end»:=104#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 72 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 72#usize 104#usize (by decide)
    (by rw [length];decide)
  simpa only [show (72#usize).val=72 from rfl,
    show (104#usize).val=104 from rfl,Nat.reduceSub] using call
#print axioms pool
theorem mint : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=104#usize,«end»:=136#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 104 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 104#usize 136#usize (by decide)
    (by rw [length];decide)
  simpa only [show (104#usize).val=104 from rfl,
    show (136#usize).val=136 from rfl,Nat.reduceSub] using call
#print axioms mint
theorem token : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=136#usize,«end»:=168#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 136 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 136#usize 168#usize (by decide)
    (by rw [length];decide)
  simpa only [show (136#usize).val=136 from rfl,
    show (168#usize).val=168 from rfl,Nat.reduceSub] using call
#print axioms token
theorem asset : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=168#usize,«end»:=172#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 168 4) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 168#usize 172#usize (by decide)
    (by rw [length];decide)
  simpa only [show (168#usize).val=168 from rfl,
    show (172#usize).val=172 from rfl,Nat.reduceSub] using call
#print axioms asset
theorem identity_reserved1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=172#usize,«end»:=176#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 172 4) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 172#usize 176#usize (by decide)
    (by rw [length];decide)
  simpa only [show (172#usize).val=172 from rfl,
    show (176#usize).val=176 from rfl,Nat.reduceSub] using call
#print axioms identity_reserved1
theorem domain : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=176#usize,«end»:=208#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 176 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 176#usize 208#usize (by decide)
    (by rw [length];decide)
  simpa only [show (176#usize).val=176 from rfl,
    show (208#usize).val=208 from rfl,Nat.reduceSub] using call
#print axioms domain
theorem policy_magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=208#usize,«end»:=212#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 208 4) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 208#usize 212#usize (by decide)
    (by rw [length];decide)
  simpa only [show (208#usize).val=208 from rfl,
    show (212#usize).val=212 from rfl,Nat.reduceSub] using call
#print axioms policy_magic
theorem policy_version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=212#usize,«end»:=213#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 212 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 212#usize 213#usize (by decide)
    (by rw [length];decide)
  simpa only [show (212#usize).val=212 from rfl,
    show (213#usize).val=213 from rfl,Nat.reduceSub] using call
#print axioms policy_version
theorem policy_flags : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=213#usize,«end»:=214#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 213 1) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 213#usize 214#usize (by decide)
    (by rw [length];decide)
  simpa only [show (213#usize).val=213 from rfl,
    show (214#usize).val=214 from rfl,Nat.reduceSub] using call
#print axioms policy_flags
theorem policy_reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=214#usize,«end»:=216#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 214 2) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 214#usize 216#usize (by decide)
    (by rw [length];decide)
  simpa only [show (214#usize).val=214 from rfl,
    show (216#usize).val=216 from rfl,Nat.reduceSub] using call
#print axioms policy_reserved
theorem registry_program : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=216#usize,«end»:=248#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 216 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 216#usize 248#usize (by decide)
    (by rw [length];decide)
  simpa only [show (216#usize).val=216 from rfl,
    show (248#usize).val=248 from rfl,Nat.reduceSub] using call
#print axioms registry_program
theorem registry_authority : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=248#usize,«end»:=280#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 248 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 248#usize 280#usize (by decide)
    (by rw [length];decide)
  simpa only [show (248#usize).val=248 from rfl,
    show (280#usize).val=280 from rfl,Nat.reduceSub] using call
#print axioms registry_authority
theorem policy_binding : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=280#usize,«end»:=312#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 280 32) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 280#usize 312#usize (by decide)
    (by rw [length];decide)
  simpa only [show (280#usize).val=280 from rfl,
    show (312#usize).val=312 from rfl,Nat.reduceSub] using call
#print axioms policy_binding
theorem reserved1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=312#usize,«end»:=320#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 312 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 312#usize 320#usize (by decide)
    (by rw [length];decide)
  simpa only [show (312#usize).val=312 from rfl,
    show (320#usize).val=320 from rfl,Nat.reduceSub] using call
#print axioms reserved1
theorem last_sequence_0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=320#usize,«end»:=328#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 320 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 320#usize 328#usize (by decide)
    (by rw [length];decide)
  simpa only [show (320#usize).val=320 from rfl,
    show (328#usize).val=328 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_0
theorem last_sequence_1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=328#usize,«end»:=336#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 328 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 328#usize 336#usize (by decide)
    (by rw [length];decide)
  simpa only [show (328#usize).val=328 from rfl,
    show (336#usize).val=336 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_1
theorem last_sequence_2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=336#usize,«end»:=344#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 336 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 336#usize 344#usize (by decide)
    (by rw [length];decide)
  simpa only [show (336#usize).val=336 from rfl,
    show (344#usize).val=344 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_2
theorem last_sequence_3 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=344#usize,«end»:=352#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 344 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 344#usize 352#usize (by decide)
    (by rw [length];decide)
  simpa only [show (344#usize).val=344 from rfl,
    show (352#usize).val=352 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_3
theorem last_sequence_4 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=352#usize,«end»:=360#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 352 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 352#usize 360#usize (by decide)
    (by rw [length];decide)
  simpa only [show (352#usize).val=352 from rfl,
    show (360#usize).val=360 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_4
theorem last_sequence_5 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=360#usize,«end»:=368#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 360 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 360#usize 368#usize (by decide)
    (by rw [length];decide)
  simpa only [show (360#usize).val=360 from rfl,
    show (368#usize).val=368 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_5
theorem last_sequence_6 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=368#usize,«end»:=376#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 368 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 368#usize 376#usize (by decide)
    (by rw [length];decide)
  simpa only [show (368#usize).val=368 from rfl,
    show (376#usize).val=376 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_6
theorem last_sequence_7 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataMaster.value {start:=376#usize,«end»:=384#usize}=
    ok (JHg_FieldRead.segment JHg_DataMaster.value 376 8) := by
  have call := JHg_FieldRead.read JHg_DataMaster.value 376#usize 384#usize (by decide)
    (by rw [length];decide)
  simpa only [show (376#usize).val=376 from rfl,
    show (384#usize).val=384 from rfl,Nat.reduceSub] using call
#print axioms last_sequence_7
end AspisR1.JHg_ReadMaster
