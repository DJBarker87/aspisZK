import R1Z.PV_RunJoin_BankAggregate18
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankTable19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17 BuilderRecordsArray

def flat (cell : Nat → Nat → U32) : PV_RunJoin_BankReads18.Flat :=
  tabulate 16384#usize (fun k => cell (k/1024) (k%1024))

def columns (cell : Nat → Nat → U32) : Columns :=
  tabulate 16#usize (PV_Src_Forest_Columns.column (flat cell))

theorem read (cell : Nat → Nat → U32) (block row lane : Usize)
    (hb : block.val < 57) (hr : row.val < 16) (hl : lane.val < 16) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      (columns cell).val[lane.val]! (rowIndex block row) =
      ok (cell lane.val (block.val*16+row.val)) := by
  rw [columns,PV_RunJoin_BankReads18.read _ block row lane hb hr hl]
  have hi : lane.val*1024+(block.val*16+row.val) < (16384#usize : Usize).val := by simp;omega
  rw [flat,tabulate_get _ _ _ hi]
  have hd : (lane.val*1024+(block.val*16+row.val))/1024 = lane.val := by omega
  have hm : (lane.val*1024+(block.val*16+row.val))%1024 = block.val*16+row.val := by omega
  rw [hd,hm]
#print axioms read

def late (block : Nat) : Prop := 34 ≤ block ∧ block < 54
instance (block : Nat) : Decidable (late block) := inferInstanceAs (Decidable (34 ≤ block ∧ block < 54))

def stableCells (cell : Nat → Nat → U32) (lane row : Nat) : U32 :=
  if late (row/16) then 0#u32 else cell lane row

def lateCells (cell : Nat → Nat → U32) (lane row : Nat) : U32 :=
  if late (row/16) then cell lane row else 0#u32

def banks (cell : Nat → Nat → U32) : pair_forest_copy_builder.CopyBanks :=
  ⟨columns (stableCells cell),columns (lateCells cell),columns cell⟩

theorem selected_read (cell : Nat → Nat → U32) (block row lane : Usize)
    (hb : block.val < 57) (hr : row.val < 16) (hl : lane.val < 16) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      (PV_RunJoin_BankAggregate18.columns (banks cell) block).val[lane.val]!
        (rowIndex block row) = ok (cell lane.val (block.val*16+row.val)) := by
  have hd : (block.val*16+row.val)/16 = block.val := by omega
  unfold PV_RunJoin_BankAggregate18.columns banks
  by_cases hc : 34 ≤ block.val ∧ block.val < 54
  · rw [if_pos hc,read _ _ _ _ hb hr hl]
    simp only [lateCells,hd,late,if_pos hc]
  · rw [if_neg hc,read _ _ _ _ hb hr hl]
    simp only [stableCells,hd,late,if_neg hc]
#print axioms selected_read
def cells (data : Nat → Nat → State) (lane row : Nat) : U32 :=
  (data (row/16) (row%16)).val[lane]!

theorem data_read (data : Nat → Nat → State) (block row lane : Usize)
    (hb : block.val < 57) (hr : row.val < 16) (hl : lane.val < 16) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      (PV_RunJoin_BankAggregate18.columns (banks (cells data)) block).val[lane.val]!
        (rowIndex block row) = ok (data block.val row.val).val[lane.val]! := by
  rw [selected_read _ _ _ _ hb hr hl]
  have hd : (block.val*16+row.val)/16 = block.val := by omega
  have hm : (block.val*16+row.val)%16 = row.val := by omega
  simp only [cells,hd,hm]
#print axioms data_read

theorem bounded (n : Nat) (hn : n ≤ 1024) (P : Usize → Prop)
    (small : ∀ j : Fin n, P (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)))
    (i : Usize) (hi : i.val < n) : P i := by
  let j : Fin n := ⟨i.val,hi⟩
  have he : i = Usize.ofNatCore j.val (by have := j.isLt;scalar_tac) := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [he]
  exact small j
#print axioms bounded
end R1Z.PV_RunJoin_BankTable19
