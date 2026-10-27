import R1Z.PV_RunJoin_BankBlock18
import R1Z.PV_Src_Forest_Columns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankReads18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17 BuilderRecordsArray
abbrev Flat := Array U32 16384#usize

theorem index_value (block row : Usize) (hb : block.val < 57) (hr : row.val < 16) :
    (rowIndex block row).val = block.val*16+row.val := by
  unfold rowIndex
  have hm : (Usize.wrapping_mul block 16#usize).val = block.val*16 := by
    rw [umul _ _ (by simp;omega)]
    rfl
  rw [uadd _ _ (by rw [hm];simp;omega),hm]
#print axioms index_value

theorem read (flat : Flat) (block row lane : Usize)
    (hb : block.val < 57) (hr : row.val < 16) (hl : lane.val < 16) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      (tabulate 16#usize (PV_Src_Forest_Columns.column flat)).val[lane.val]!
        (rowIndex block row) = ok flat.val[lane.val*1024+(block.val*16+row.val)]! := by
  rw [tabulate_get _ _ _ (by simpa using hl)]
  have hv := index_value block row hb hr
  rw [PV_Src_Forest_BankCells.vec_index _ _ (by
    rw [PV_Src_Forest_Columns.column_length flat lane.val hl,hv];omega)]
  rw [PV_Src_Forest_Columns.column_at flat lane.val _ hl (by rw [hv];omega),hv]
#print axioms read
end R1Z.PV_RunJoin_BankReads18
