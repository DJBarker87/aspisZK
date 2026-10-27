import JHg_DataForest
import JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_ReadForest
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataForest.value JHg_FieldRead.segment
theorem length : JHg_DataForest.value.val.length=192 := by unfold JHg_DataForest.value;exact JHg_DataForest.length
#print axioms length
theorem magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=0#usize,«end»:=4#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 0 4) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 0#usize 4#usize (by decide)
    (by rw [length];decide)
  simpa only [show (0#usize).val=0 from rfl,
    show (4#usize).val=4 from rfl,Nat.reduceSub] using call
#print axioms magic
theorem version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=4#usize,«end»:=5#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 4 1) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 4#usize 5#usize (by decide)
    (by rw [length];decide)
  simpa only [show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,Nat.reduceSub] using call
#print axioms version
theorem lanes : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=5#usize,«end»:=6#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 5 1) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 5#usize 6#usize (by decide)
    (by rw [length];decide)
  simpa only [show (5#usize).val=5 from rfl,
    show (6#usize).val=6 from rfl,Nat.reduceSub] using call
#print axioms lanes
theorem encoding : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=6#usize,«end»:=7#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 6 1) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 6#usize 7#usize (by decide)
    (by rw [length];decide)
  simpa only [show (6#usize).val=6 from rfl,
    show (7#usize).val=7 from rfl,Nat.reduceSub] using call
#print axioms encoding
theorem bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=7#usize,«end»:=8#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 7 1) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 7#usize 8#usize (by decide)
    (by rw [length];decide)
  simpa only [show (7#usize).val=7 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub] using call
#print axioms bump
theorem master : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=8#usize,«end»:=40#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 8 32) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 8#usize 40#usize (by decide)
    (by rw [length];decide)
  simpa only [show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,Nat.reduceSub] using call
#print axioms master
theorem domain : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=40#usize,«end»:=72#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 40 32) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 40#usize 72#usize (by decide)
    (by rw [length];decide)
  simpa only [show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,Nat.reduceSub] using call
#print axioms domain
theorem sequence : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=72#usize,«end»:=80#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 72 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 72#usize 80#usize (by decide)
    (by rw [length];decide)
  simpa only [show (72#usize).val=72 from rfl,
    show (80#usize).val=80 from rfl,Nat.reduceSub] using call
#print axioms sequence
theorem root : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=80#usize,«end»:=112#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 80 32) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 80#usize 112#usize (by decide)
    (by rw [length];decide)
  simpa only [show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,Nat.reduceSub] using call
#print axioms root
theorem lane_sequence_0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=112#usize,«end»:=120#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 112 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 112#usize 120#usize (by decide)
    (by rw [length];decide)
  simpa only [show (112#usize).val=112 from rfl,
    show (120#usize).val=120 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_0
theorem lane_sequence_1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=120#usize,«end»:=128#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 120 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 120#usize 128#usize (by decide)
    (by rw [length];decide)
  simpa only [show (120#usize).val=120 from rfl,
    show (128#usize).val=128 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_1
theorem lane_sequence_2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=128#usize,«end»:=136#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 128 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 128#usize 136#usize (by decide)
    (by rw [length];decide)
  simpa only [show (128#usize).val=128 from rfl,
    show (136#usize).val=136 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_2
theorem lane_sequence_3 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=136#usize,«end»:=144#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 136 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 136#usize 144#usize (by decide)
    (by rw [length];decide)
  simpa only [show (136#usize).val=136 from rfl,
    show (144#usize).val=144 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_3
theorem lane_sequence_4 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=144#usize,«end»:=152#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 144 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 144#usize 152#usize (by decide)
    (by rw [length];decide)
  simpa only [show (144#usize).val=144 from rfl,
    show (152#usize).val=152 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_4
theorem lane_sequence_5 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=152#usize,«end»:=160#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 152 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 152#usize 160#usize (by decide)
    (by rw [length];decide)
  simpa only [show (152#usize).val=152 from rfl,
    show (160#usize).val=160 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_5
theorem lane_sequence_6 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=160#usize,«end»:=168#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 160 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 160#usize 168#usize (by decide)
    (by rw [length];decide)
  simpa only [show (160#usize).val=160 from rfl,
    show (168#usize).val=168 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_6
theorem lane_sequence_7 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=168#usize,«end»:=176#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 168 8) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 168#usize 176#usize (by decide)
    (by rw [length];decide)
  simpa only [show (168#usize).val=168 from rfl,
    show (176#usize).val=176 from rfl,Nat.reduceSub] using call
#print axioms lane_sequence_7
theorem reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHg_DataForest.value {start:=176#usize,«end»:=192#usize}=
    ok (JHg_FieldRead.segment JHg_DataForest.value 176 16) := by
  have call := JHg_FieldRead.read JHg_DataForest.value 176#usize 192#usize (by decide)
    (by rw [length];decide)
  simpa only [show (176#usize).val=176 from rfl,
    show (192#usize).val=192 from rfl,Nat.reduceSub] using call
#print axioms reserved
end AspisR1.JHg_ReadForest
