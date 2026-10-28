import NDO_JFo_AuthBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Header
open Aeneas Aeneas.Std Result AspisR1Stage2

def zeros : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by simp;scalar_tac⟩

theorem reserved : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.checkpoint {start:=11#usize,«end»:=16#usize}=ok zeros := by
  have selected : JFq_Range.segment 11 5 (by decide)=zeros := by
    apply Subtype.ext
    rfl
  have call:=JFq_Range.read 11#usize 16#usize (by decide) (by decide)
  change _=ok (JFq_Range.segment 11 5 (by decide)) at call
  rw [selected] at call
  exact call

theorem iterator : core.slice.Slice.iter zeros=ok ⟨zeros,0⟩ := rfl

theorem scanned : CheckpointBytes4Ops.headerAny ⟨zeros,0⟩=ok (false,⟨zeros,5⟩) := by
  rfl

theorem tag : Slice.index_usize JFx_NativeBytes.checkpoint 8#usize=ok 2#u8 :=
  JFo_AuthBytes.byte 8#usize (by decide) 2#u8 rfl

theorem cursor : Slice.index_usize JFx_NativeBytes.checkpoint 9#usize=ok 10#u8 :=
  JFo_AuthBytes.byte 9#usize (by decide) 10#u8 rfl

theorem version : Slice.index_usize JFx_NativeBytes.checkpoint 10#usize=ok 1#u8 :=
  JFo_AuthBytes.byte 10#usize (by decide) 1#u8 rfl

theorem magic : CheckpointBytes4Ops.ne core.cmp.PartialEqU8
    JFo_AuthBytes.header JFo_AuthBytes.magic=ok false := JFq_Compare.ne _ _ rfl

#print axioms reserved
#print axioms iterator
#print axioms scanned
#print axioms tag
#print axioms cursor
#print axioms version
#print axioms magic
end AspisR1.JFo_Header
end
