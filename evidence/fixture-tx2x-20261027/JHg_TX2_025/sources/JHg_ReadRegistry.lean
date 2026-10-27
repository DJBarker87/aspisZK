import JHb_DataRegistry
import JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_ReadRegistry
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataRegistry.value JHg_FieldRead.segment
theorem length : JHb_DataRegistry.value.val.length=256 := by unfold JHb_DataRegistry.value;exact JHb_DataRegistry.length
#print axioms length
theorem magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=0#usize,«end»:=4#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 0 4) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 0#usize 4#usize (by decide)
    (by rw [length];decide)
  simpa only [show (0#usize).val=0 from rfl,
    show (4#usize).val=4 from rfl,Nat.reduceSub] using call
#print axioms magic
theorem version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=4#usize,«end»:=5#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 4 1) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 4#usize 5#usize (by decide)
    (by rw [length];decide)
  simpa only [show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,Nat.reduceSub] using call
#print axioms version
theorem flags : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=5#usize,«end»:=6#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 5 1) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 5#usize 6#usize (by decide)
    (by rw [length];decide)
  simpa only [show (5#usize).val=5 from rfl,
    show (6#usize).val=6 from rfl,Nat.reduceSub] using call
#print axioms flags
theorem mode : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=6#usize,«end»:=7#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 6 1) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 6#usize 7#usize (by decide)
    (by rw [length];decide)
  simpa only [show (6#usize).val=6 from rfl,
    show (7#usize).val=7 from rfl,Nat.reduceSub] using call
#print axioms mode
theorem bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=7#usize,«end»:=8#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 7 1) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 7#usize 8#usize (by decide)
    (by rw [length];decide)
  simpa only [show (7#usize).val=7 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub] using call
#print axioms bump
theorem pool : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=8#usize,«end»:=40#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 8 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 8#usize 40#usize (by decide)
    (by rw [length];decide)
  simpa only [show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,Nat.reduceSub] using call
#print axioms pool
theorem authority : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=40#usize,«end»:=72#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 40 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 40#usize 72#usize (by decide)
    (by rw [length];decide)
  simpa only [show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,Nat.reduceSub] using call
#print axioms authority
theorem policy : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=72#usize,«end»:=104#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 72 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 72#usize 104#usize (by decide)
    (by rw [length];decide)
  simpa only [show (72#usize).val=72 from rfl,
    show (104#usize).val=104 from rfl,Nat.reduceSub] using call
#print axioms policy
theorem generation : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=104#usize,«end»:=112#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 104 8) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 104#usize 112#usize (by decide)
    (by rw [length];decide)
  simpa only [show (104#usize).val=104 from rfl,
    show (112#usize).val=112 from rfl,Nat.reduceSub] using call
#print axioms generation
theorem delay : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=112#usize,«end»:=120#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 112 8) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 112#usize 120#usize (by decide)
    (by rw [length];decide)
  simpa only [show (112#usize).val=112 from rfl,
    show (120#usize).val=120 from rfl,Nat.reduceSub] using call
#print axioms delay
theorem program : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=120#usize,«end»:=152#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 120 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 120#usize 152#usize (by decide)
    (by rw [length];decide)
  simpa only [show (120#usize).val=120 from rfl,
    show (152#usize).val=152 from rfl,Nat.reduceSub] using call
#print axioms program
theorem loader : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=152#usize,«end»:=184#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 152 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 152#usize 184#usize (by decide)
    (by rw [length];decide)
  simpa only [show (152#usize).val=152 from rfl,
    show (184#usize).val=184 from rfl,Nat.reduceSub] using call
#print axioms loader
theorem programdata : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=184#usize,«end»:=216#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 184 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 184#usize 216#usize (by decide)
    (by rw [length];decide)
  simpa only [show (184#usize).val=184 from rfl,
    show (216#usize).val=216 from rfl,Nat.reduceSub] using call
#print axioms programdata
theorem executable_hash : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=216#usize,«end»:=248#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 216 32) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 216#usize 248#usize (by decide)
    (by rw [length];decide)
  simpa only [show (216#usize).val=216 from rfl,
    show (248#usize).val=248 from rfl,Nat.reduceSub] using call
#print axioms executable_hash
theorem programdata_bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=248#usize,«end»:=249#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 248 1) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 248#usize 249#usize (by decide)
    (by rw [length];decide)
  simpa only [show (248#usize).val=248 from rfl,
    show (249#usize).val=249 from rfl,Nat.reduceSub] using call
#print axioms programdata_bump
theorem reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataRegistry.value {start:=249#usize,«end»:=256#usize}=
    ok (JHg_FieldRead.segment JHb_DataRegistry.value 249 7) := by
  have call := JHg_FieldRead.read JHb_DataRegistry.value 249#usize 256#usize (by decide)
    (by rw [length];decide)
  simpa only [show (249#usize).val=249 from rfl,
    show (256#usize).val=256 from rfl,Nat.reduceSub] using call
#print axioms reserved
end AspisR1.JHg_ReadRegistry
