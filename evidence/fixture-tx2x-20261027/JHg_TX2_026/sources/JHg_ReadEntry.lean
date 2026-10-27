import JHb_DataEntry
import JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_ReadEntry
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataEntry.value JHg_FieldRead.segment
theorem length : JHb_DataEntry.value.val.length=320 := by unfold JHb_DataEntry.value;exact JHb_DataEntry.length
#print axioms length
theorem magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=0#usize,«end»:=4#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 0 4) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 0#usize 4#usize (by decide)
    (by rw [length];decide)
  simpa only [show (0#usize).val=0 from rfl,
    show (4#usize).val=4 from rfl,Nat.reduceSub] using call
#print axioms magic
theorem version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=4#usize,«end»:=5#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 4 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 4#usize 5#usize (by decide)
    (by rw [length];decide)
  simpa only [show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,Nat.reduceSub] using call
#print axioms version
theorem status : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=5#usize,«end»:=6#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 5 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 5#usize 6#usize (by decide)
    (by rw [length];decide)
  simpa only [show (5#usize).val=5 from rfl,
    show (6#usize).val=6 from rfl,Nat.reduceSub] using call
#print axioms status
theorem statement_version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=6#usize,«end»:=7#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 6 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 6#usize 7#usize (by decide)
    (by rw [length];decide)
  simpa only [show (6#usize).val=6 from rfl,
    show (7#usize).val=7 from rfl,Nat.reduceSub] using call
#print axioms statement_version
theorem mode : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=7#usize,«end»:=8#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 7 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 7#usize 8#usize (by decide)
    (by rw [length];decide)
  simpa only [show (7#usize).val=7 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub] using call
#print axioms mode
theorem pool : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=8#usize,«end»:=40#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 8 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 8#usize 40#usize (by decide)
    (by rw [length];decide)
  simpa only [show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,Nat.reduceSub] using call
#print axioms pool
theorem verifier : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=40#usize,«end»:=72#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 40 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 40#usize 72#usize (by decide)
    (by rw [length];decide)
  simpa only [show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,Nat.reduceSub] using call
#print axioms verifier
theorem profile : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=72#usize,«end»:=104#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 72 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 72#usize 104#usize (by decide)
    (by rw [length];decide)
  simpa only [show (72#usize).val=72 from rfl,
    show (104#usize).val=104 from rfl,Nat.reduceSub] using call
#print axioms profile
theorem release : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=104#usize,«end»:=136#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 104 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 104#usize 136#usize (by decide)
    (by rw [length];decide)
  simpa only [show (104#usize).val=104 from rfl,
    show (136#usize).val=136 from rfl,Nat.reduceSub] using call
#print axioms release
theorem loader : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=136#usize,«end»:=168#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 136 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 136#usize 168#usize (by decide)
    (by rw [length];decide)
  simpa only [show (136#usize).val=136 from rfl,
    show (168#usize).val=168 from rfl,Nat.reduceSub] using call
#print axioms loader
theorem programdata : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=168#usize,«end»:=200#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 168 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 168#usize 200#usize (by decide)
    (by rw [length];decide)
  simpa only [show (168#usize).val=168 from rfl,
    show (200#usize).val=200 from rfl,Nat.reduceSub] using call
#print axioms programdata
theorem executable_hash : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=200#usize,«end»:=232#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 200 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 200#usize 232#usize (by decide)
    (by rw [length];decide)
  simpa only [show (200#usize).val=200 from rfl,
    show (232#usize).val=232 from rfl,Nat.reduceSub] using call
#print axioms executable_hash
theorem upgrade_authority : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=232#usize,«end»:=264#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 232 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 232#usize 264#usize (by decide)
    (by rw [length];decide)
  simpa only [show (232#usize).val=232 from rfl,
    show (264#usize).val=264 from rfl,Nat.reduceSub] using call
#print axioms upgrade_authority
theorem activation : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=264#usize,«end»:=272#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 264 8) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 264#usize 272#usize (by decide)
    (by rw [length];decide)
  simpa only [show (264#usize).val=264 from rfl,
    show (272#usize).val=272 from rfl,Nat.reduceSub] using call
#print axioms activation
theorem retirement : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=272#usize,«end»:=280#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 272 8) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 272#usize 280#usize (by decide)
    (by rw [length];decide)
  simpa only [show (272#usize).val=272 from rfl,
    show (280#usize).val=280 from rfl,Nat.reduceSub] using call
#print axioms retirement
theorem policy : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=280#usize,«end»:=312#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 280 32) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 280#usize 312#usize (by decide)
    (by rw [length];decide)
  simpa only [show (280#usize).val=280 from rfl,
    show (312#usize).val=312 from rfl,Nat.reduceSub] using call
#print axioms policy
theorem bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=312#usize,«end»:=313#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 312 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 312#usize 313#usize (by decide)
    (by rw [length];decide)
  simpa only [show (312#usize).val=312 from rfl,
    show (313#usize).val=313 from rfl,Nat.reduceSub] using call
#print axioms bump
theorem programdata_bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=313#usize,«end»:=314#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 313 1) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 313#usize 314#usize (by decide)
    (by rw [length];decide)
  simpa only [show (313#usize).val=313 from rfl,
    show (314#usize).val=314 from rfl,Nat.reduceSub] using call
#print axioms programdata_bump
theorem reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataEntry.value {start:=314#usize,«end»:=320#usize}=
    ok (JHg_FieldRead.segment JHb_DataEntry.value 314 6) := by
  have call := JHg_FieldRead.read JHb_DataEntry.value 314#usize 320#usize (by decide)
    (by rw [length];decide)
  simpa only [show (314#usize).val=314 from rfl,
    show (320#usize).val=320 from rfl,Nat.reduceSub] using call
#print axioms reserved
end AspisR1.JHg_ReadEntry
