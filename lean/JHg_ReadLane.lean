import JHb_DataLane
import JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHg_ReadLane
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value JHg_FieldRead.segment
theorem length : JHb_DataLane.value.val.length=768 := by unfold JHb_DataLane.value;exact JHb_DataLane.length
#print axioms length
theorem magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=0#usize,«end»:=4#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 0 4) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 0#usize 4#usize (by decide)
    (by rw [length];decide)
  simpa only [show (0#usize).val=0 from rfl,
    show (4#usize).val=4 from rfl,Nat.reduceSub] using call
#print axioms magic
theorem version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=4#usize,«end»:=5#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 4 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 4#usize 5#usize (by decide)
    (by rw [length];decide)
  simpa only [show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,Nat.reduceSub] using call
#print axioms version
theorem lane : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=5#usize,«end»:=6#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 5 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 5#usize 6#usize (by decide)
    (by rw [length];decide)
  simpa only [show (5#usize).val=5 from rfl,
    show (6#usize).val=6 from rfl,Nat.reduceSub] using call
#print axioms lane
theorem lanes : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=6#usize,«end»:=7#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 6 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 6#usize 7#usize (by decide)
    (by rw [length];decide)
  simpa only [show (6#usize).val=6 from rfl,
    show (7#usize).val=7 from rfl,Nat.reduceSub] using call
#print axioms lanes
theorem depth : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=7#usize,«end»:=8#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 7 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 7#usize 8#usize (by decide)
    (by rw [length];decide)
  simpa only [show (7#usize).val=7 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub] using call
#print axioms depth
theorem format : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=8#usize,«end»:=40#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 8 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 8#usize 40#usize (by decide)
    (by rw [length];decide)
  simpa only [show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,Nat.reduceSub] using call
#print axioms format
theorem master : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=40#usize,«end»:=72#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 40 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 40#usize 72#usize (by decide)
    (by rw [length];decide)
  simpa only [show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,Nat.reduceSub] using call
#print axioms master
theorem bump : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=72#usize,«end»:=73#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 72 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 72#usize 73#usize (by decide)
    (by rw [length];decide)
  simpa only [show (72#usize).val=72 from rfl,
    show (73#usize).val=73 from rfl,Nat.reduceSub] using call
#print axioms bump
theorem reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=73#usize,«end»:=80#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 73 7) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 73#usize 80#usize (by decide)
    (by rw [length];decide)
  simpa only [show (73#usize).val=73 from rfl,
    show (80#usize).val=80 from rfl,Nat.reduceSub] using call
#print axioms reserved
theorem tree_magic : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=80#usize,«end»:=84#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 80 4) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 80#usize 84#usize (by decide)
    (by rw [length];decide)
  simpa only [show (80#usize).val=80 from rfl,
    show (84#usize).val=84 from rfl,Nat.reduceSub] using call
#print axioms tree_magic
theorem tree_version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=84#usize,«end»:=85#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 84 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 84#usize 85#usize (by decide)
    (by rw [length];decide)
  simpa only [show (84#usize).val=84 from rfl,
    show (85#usize).val=85 from rfl,Nat.reduceSub] using call
#print axioms tree_version
theorem tree_depth : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=85#usize,«end»:=86#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 85 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 85#usize 86#usize (by decide)
    (by rw [length];decide)
  simpa only [show (85#usize).val=85 from rfl,
    show (86#usize).val=86 from rfl,Nat.reduceSub] using call
#print axioms tree_depth
theorem tree_hash_version : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=86#usize,«end»:=87#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 86 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 86#usize 87#usize (by decide)
    (by rw [length];decide)
  simpa only [show (86#usize).val=86 from rfl,
    show (87#usize).val=87 from rfl,Nat.reduceSub] using call
#print axioms tree_hash_version
theorem tree_encoding : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=87#usize,«end»:=88#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 87 1) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 87#usize 88#usize (by decide)
    (by rw [length];decide)
  simpa only [show (87#usize).val=87 from rfl,
    show (88#usize).val=88 from rfl,Nat.reduceSub] using call
#print axioms tree_encoding
theorem next_index : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=88#usize,«end»:=96#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 88 8) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 88#usize 96#usize (by decide)
    (by rw [length];decide)
  simpa only [show (88#usize).val=88 from rfl,
    show (96#usize).val=96 from rfl,Nat.reduceSub] using call
#print axioms next_index
theorem root : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=96#usize,«end»:=128#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 96 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 96#usize 128#usize (by decide)
    (by rw [length];decide)
  simpa only [show (96#usize).val=96 from rfl,
    show (128#usize).val=128 from rfl,Nat.reduceSub] using call
#print axioms root
theorem frontier_0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=128#usize,«end»:=160#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 128 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 128#usize 160#usize (by decide)
    (by rw [length];decide)
  simpa only [show (128#usize).val=128 from rfl,
    show (160#usize).val=160 from rfl,Nat.reduceSub] using call
#print axioms frontier_0
theorem frontier_1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=160#usize,«end»:=192#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 160 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 160#usize 192#usize (by decide)
    (by rw [length];decide)
  simpa only [show (160#usize).val=160 from rfl,
    show (192#usize).val=192 from rfl,Nat.reduceSub] using call
#print axioms frontier_1
theorem frontier_2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=192#usize,«end»:=224#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 192 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 192#usize 224#usize (by decide)
    (by rw [length];decide)
  simpa only [show (192#usize).val=192 from rfl,
    show (224#usize).val=224 from rfl,Nat.reduceSub] using call
#print axioms frontier_2
theorem frontier_3 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=224#usize,«end»:=256#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 224 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 224#usize 256#usize (by decide)
    (by rw [length];decide)
  simpa only [show (224#usize).val=224 from rfl,
    show (256#usize).val=256 from rfl,Nat.reduceSub] using call
#print axioms frontier_3
theorem frontier_4 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=256#usize,«end»:=288#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 256 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 256#usize 288#usize (by decide)
    (by rw [length];decide)
  simpa only [show (256#usize).val=256 from rfl,
    show (288#usize).val=288 from rfl,Nat.reduceSub] using call
#print axioms frontier_4
theorem frontier_5 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=288#usize,«end»:=320#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 288 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 288#usize 320#usize (by decide)
    (by rw [length];decide)
  simpa only [show (288#usize).val=288 from rfl,
    show (320#usize).val=320 from rfl,Nat.reduceSub] using call
#print axioms frontier_5
theorem frontier_6 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=320#usize,«end»:=352#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 320 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 320#usize 352#usize (by decide)
    (by rw [length];decide)
  simpa only [show (320#usize).val=320 from rfl,
    show (352#usize).val=352 from rfl,Nat.reduceSub] using call
#print axioms frontier_6
theorem frontier_7 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=352#usize,«end»:=384#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 352 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 352#usize 384#usize (by decide)
    (by rw [length];decide)
  simpa only [show (352#usize).val=352 from rfl,
    show (384#usize).val=384 from rfl,Nat.reduceSub] using call
#print axioms frontier_7
theorem frontier_8 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=384#usize,«end»:=416#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 384 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 384#usize 416#usize (by decide)
    (by rw [length];decide)
  simpa only [show (384#usize).val=384 from rfl,
    show (416#usize).val=416 from rfl,Nat.reduceSub] using call
#print axioms frontier_8
theorem frontier_9 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=416#usize,«end»:=448#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 416 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 416#usize 448#usize (by decide)
    (by rw [length];decide)
  simpa only [show (416#usize).val=416 from rfl,
    show (448#usize).val=448 from rfl,Nat.reduceSub] using call
#print axioms frontier_9
theorem frontier_10 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=448#usize,«end»:=480#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 448 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 448#usize 480#usize (by decide)
    (by rw [length];decide)
  simpa only [show (448#usize).val=448 from rfl,
    show (480#usize).val=480 from rfl,Nat.reduceSub] using call
#print axioms frontier_10
theorem frontier_11 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=480#usize,«end»:=512#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 480 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 480#usize 512#usize (by decide)
    (by rw [length];decide)
  simpa only [show (480#usize).val=480 from rfl,
    show (512#usize).val=512 from rfl,Nat.reduceSub] using call
#print axioms frontier_11
theorem frontier_12 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=512#usize,«end»:=544#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 512 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 512#usize 544#usize (by decide)
    (by rw [length];decide)
  simpa only [show (512#usize).val=512 from rfl,
    show (544#usize).val=544 from rfl,Nat.reduceSub] using call
#print axioms frontier_12
theorem frontier_13 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=544#usize,«end»:=576#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 544 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 544#usize 576#usize (by decide)
    (by rw [length];decide)
  simpa only [show (544#usize).val=544 from rfl,
    show (576#usize).val=576 from rfl,Nat.reduceSub] using call
#print axioms frontier_13
theorem frontier_14 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=576#usize,«end»:=608#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 576 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 576#usize 608#usize (by decide)
    (by rw [length];decide)
  simpa only [show (576#usize).val=576 from rfl,
    show (608#usize).val=608 from rfl,Nat.reduceSub] using call
#print axioms frontier_14
theorem frontier_15 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=608#usize,«end»:=640#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 608 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 608#usize 640#usize (by decide)
    (by rw [length];decide)
  simpa only [show (608#usize).val=608 from rfl,
    show (640#usize).val=640 from rfl,Nat.reduceSub] using call
#print axioms frontier_15
theorem frontier_16 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=640#usize,«end»:=672#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 640 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 640#usize 672#usize (by decide)
    (by rw [length];decide)
  simpa only [show (640#usize).val=640 from rfl,
    show (672#usize).val=672 from rfl,Nat.reduceSub] using call
#print axioms frontier_16
theorem frontier_17 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=672#usize,«end»:=704#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 672 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 672#usize 704#usize (by decide)
    (by rw [length];decide)
  simpa only [show (672#usize).val=672 from rfl,
    show (704#usize).val=704 from rfl,Nat.reduceSub] using call
#print axioms frontier_17
theorem frontier_18 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=704#usize,«end»:=736#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 704 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 704#usize 736#usize (by decide)
    (by rw [length];decide)
  simpa only [show (704#usize).val=704 from rfl,
    show (736#usize).val=736 from rfl,Nat.reduceSub] using call
#print axioms frontier_18
theorem frontier_19 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_DataLane.value {start:=736#usize,«end»:=768#usize}=
    ok (JHg_FieldRead.segment JHb_DataLane.value 736 32) := by
  have call := JHg_FieldRead.read JHb_DataLane.value 736#usize 768#usize (by decide)
    (by rw [length];decide)
  simpa only [show (736#usize).val=736 from rfl,
    show (768#usize).val=768 from rfl,Nat.reduceSub] using call
#print axioms frontier_19
end AspisR1.JHg_ReadLane
