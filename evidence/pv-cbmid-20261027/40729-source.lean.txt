-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_59]:
    Source: 'reference.rs', lines 4197:0-4225:1
    Visibility: public -/
def reference.cells_chunk_59
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 993#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 995#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 996#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 997#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 999#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 1000#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 1001#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 1003#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 1004#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 1005#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 1007#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 1008#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 1009#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 1010#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 1011#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 1012#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 1013#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 1014#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 1015#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 1016#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 1017#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 1018#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 1019#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 1020#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 1021#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 1022#u16, column := 15#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out26 ({ row := 1023#u16, column := 15#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk59
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 993#u16, column := 15#u8},
    {row := 995#u16, column := 15#u8},
    {row := 996#u16, column := 15#u8},
    {row := 997#u16, column := 15#u8},
    {row := 999#u16, column := 15#u8},
    {row := 1000#u16, column := 15#u8},
    {row := 1001#u16, column := 15#u8},
    {row := 1003#u16, column := 15#u8},
    {row := 1004#u16, column := 15#u8},
    {row := 1005#u16, column := 15#u8},
    {row := 1007#u16, column := 15#u8},
    {row := 1008#u16, column := 15#u8},
    {row := 1009#u16, column := 15#u8},
    {row := 1010#u16, column := 15#u8},
    {row := 1011#u16, column := 15#u8},
    {row := 1012#u16, column := 15#u8},
    {row := 1013#u16, column := 15#u8},
    {row := 1014#u16, column := 15#u8},
    {row := 1015#u16, column := 15#u8},
    {row := 1016#u16, column := 15#u8},
    {row := 1017#u16, column := 15#u8},
    {row := 1018#u16, column := 15#u8},
    {row := 1019#u16, column := 15#u8},
    {row := 1020#u16, column := 15#u8},
    {row := 1021#u16, column := 15#u8},
    {row := 1022#u16, column := 15#u8},
    {row := 1023#u16, column := 15#u8}
  ]
theorem length : literals.length = 27 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_59 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_59
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 27 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_59 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 993 15; exact (PV_CBM_PathClassification.pathFree_mod 993 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 995 15; exact (PV_CBM_PathClassification.pathFree_mod 995 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 996 15; exact (PV_CBM_PathClassification.pathFree_mod 996 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 997 15; exact (PV_CBM_PathClassification.pathFree_mod 997 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 999 15; exact (PV_CBM_PathClassification.pathFree_mod 999 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1000 15; exact (PV_CBM_PathClassification.pathFree_mod 1000 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1001 15; exact (PV_CBM_PathClassification.pathFree_mod 1001 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1003 15; exact (PV_CBM_PathClassification.pathFree_mod 1003 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1004 15; exact (PV_CBM_PathClassification.pathFree_mod 1004 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1005 15; exact (PV_CBM_PathClassification.pathFree_mod 1005 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1007 15; exact (PV_CBM_PathClassification.pathFree_mod 1007 15 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1008 15; exact (PV_CBM_ValueFree.valueFree_iff 0 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1009 15; exact (PV_CBM_ValueFree.valueFree_iff 1 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1010 15; exact (PV_CBM_ValueFree.valueFree_iff 2 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1011 15; exact (PV_CBM_ValueFree.valueFree_iff 3 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1012 15; exact (PV_CBM_ValueFree.valueFree_iff 4 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1013 15; exact (PV_CBM_ValueFree.valueFree_iff 5 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1014 15; exact (PV_CBM_ValueFree.valueFree_iff 6 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1015 15; exact (PV_CBM_ValueFree.valueFree_iff 7 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1016 15; exact (PV_CBM_ValueFree.valueFree_iff 8 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1017 15; exact (PV_CBM_ValueFree.valueFree_iff 9 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1018 15; exact (PV_CBM_ValueFree.valueFree_iff 10 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1019 15; exact (PV_CBM_ValueFree.valueFree_iff 11 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1020 15; exact (PV_CBM_ValueFree.valueFree_iff 12 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1021 15; exact (PV_CBM_ValueFree.valueFree_iff 13 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1022 15; exact (PV_CBM_ValueFree.valueFree_iff 14 15 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1023 15; exact (PV_CBM_ValueFree.valueFree_iff 15 15 (by decide)).mpr (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk59
