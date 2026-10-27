-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_17]:
    Source: 'reference.rs', lines 1425:0-1490:1
    Visibility: public -/
def reference.cells_chunk_17
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 964#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 967#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 968#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 971#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 972#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 975#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 976#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 979#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 980#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 983#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 984#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 987#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 988#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 991#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 992#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 995#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 996#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 999#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 1000#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 1003#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 1004#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 1007#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 1014#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 1015#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 1019#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 1021#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 1023#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 13#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 14#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 15#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 29#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 30#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 31#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 45#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 46#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 47#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 61#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 62#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 63#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 77#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 78#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 79#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 93#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 94#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 95#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 109#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 110#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 111#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 125#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 126#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 127#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 141#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 142#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 143#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 157#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 158#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 159#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 173#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 174#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 175#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 189#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 190#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 191#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 205#u16, column := 5#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk17
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 964#u16, column := 4#u8},
    {row := 967#u16, column := 4#u8},
    {row := 968#u16, column := 4#u8},
    {row := 971#u16, column := 4#u8},
    {row := 972#u16, column := 4#u8},
    {row := 975#u16, column := 4#u8},
    {row := 976#u16, column := 4#u8},
    {row := 979#u16, column := 4#u8},
    {row := 980#u16, column := 4#u8},
    {row := 983#u16, column := 4#u8},
    {row := 984#u16, column := 4#u8},
    {row := 987#u16, column := 4#u8},
    {row := 988#u16, column := 4#u8},
    {row := 991#u16, column := 4#u8},
    {row := 992#u16, column := 4#u8},
    {row := 995#u16, column := 4#u8},
    {row := 996#u16, column := 4#u8},
    {row := 999#u16, column := 4#u8},
    {row := 1000#u16, column := 4#u8},
    {row := 1003#u16, column := 4#u8},
    {row := 1004#u16, column := 4#u8},
    {row := 1007#u16, column := 4#u8},
    {row := 1014#u16, column := 4#u8},
    {row := 1015#u16, column := 4#u8},
    {row := 1019#u16, column := 4#u8},
    {row := 1021#u16, column := 4#u8},
    {row := 1023#u16, column := 4#u8},
    {row := 13#u16, column := 5#u8},
    {row := 14#u16, column := 5#u8},
    {row := 15#u16, column := 5#u8},
    {row := 29#u16, column := 5#u8},
    {row := 30#u16, column := 5#u8},
    {row := 31#u16, column := 5#u8},
    {row := 45#u16, column := 5#u8},
    {row := 46#u16, column := 5#u8},
    {row := 47#u16, column := 5#u8},
    {row := 61#u16, column := 5#u8},
    {row := 62#u16, column := 5#u8},
    {row := 63#u16, column := 5#u8},
    {row := 77#u16, column := 5#u8},
    {row := 78#u16, column := 5#u8},
    {row := 79#u16, column := 5#u8},
    {row := 93#u16, column := 5#u8},
    {row := 94#u16, column := 5#u8},
    {row := 95#u16, column := 5#u8},
    {row := 109#u16, column := 5#u8},
    {row := 110#u16, column := 5#u8},
    {row := 111#u16, column := 5#u8},
    {row := 125#u16, column := 5#u8},
    {row := 126#u16, column := 5#u8},
    {row := 127#u16, column := 5#u8},
    {row := 141#u16, column := 5#u8},
    {row := 142#u16, column := 5#u8},
    {row := 143#u16, column := 5#u8},
    {row := 157#u16, column := 5#u8},
    {row := 158#u16, column := 5#u8},
    {row := 159#u16, column := 5#u8},
    {row := 173#u16, column := 5#u8},
    {row := 174#u16, column := 5#u8},
    {row := 175#u16, column := 5#u8},
    {row := 189#u16, column := 5#u8},
    {row := 190#u16, column := 5#u8},
    {row := 191#u16, column := 5#u8},
    {row := 205#u16, column := 5#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_17 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_17
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_17 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 964 4; exact (PV_CBM_PathClassification.pathFree_mod 964 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 967 4; exact (PV_CBM_PathClassification.pathFree_mod 967 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 968 4; exact (PV_CBM_PathClassification.pathFree_mod 968 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 971 4; exact (PV_CBM_PathClassification.pathFree_mod 971 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 972 4; exact (PV_CBM_PathClassification.pathFree_mod 972 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 975 4; exact (PV_CBM_PathClassification.pathFree_mod 975 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 976 4; exact (PV_CBM_PathClassification.pathFree_mod 976 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 979 4; exact (PV_CBM_PathClassification.pathFree_mod 979 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 980 4; exact (PV_CBM_PathClassification.pathFree_mod 980 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 983 4; exact (PV_CBM_PathClassification.pathFree_mod 983 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 984 4; exact (PV_CBM_PathClassification.pathFree_mod 984 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 987 4; exact (PV_CBM_PathClassification.pathFree_mod 987 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 988 4; exact (PV_CBM_PathClassification.pathFree_mod 988 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 991 4; exact (PV_CBM_PathClassification.pathFree_mod 991 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 992 4; exact (PV_CBM_PathClassification.pathFree_mod 992 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 995 4; exact (PV_CBM_PathClassification.pathFree_mod 995 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 996 4; exact (PV_CBM_PathClassification.pathFree_mod 996 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 999 4; exact (PV_CBM_PathClassification.pathFree_mod 999 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1000 4; exact (PV_CBM_PathClassification.pathFree_mod 1000 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1003 4; exact (PV_CBM_PathClassification.pathFree_mod 1003 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1004 4; exact (PV_CBM_PathClassification.pathFree_mod 1004 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1007 4; exact (PV_CBM_PathClassification.pathFree_mod 1007 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1014 4; exact (PV_CBM_ValueFree.valueFree_iff 6 4 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1015 4; exact (PV_CBM_ValueFree.valueFree_iff 7 4 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1019 4; exact (PV_CBM_ValueFree.valueFree_iff 11 4 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1021 4; exact (PV_CBM_ValueFree.valueFree_iff 13 4 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1023 4; exact (PV_CBM_ValueFree.valueFree_iff 15 4 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 13 5; exact PV_CBM_InventoryShape.free_padding 13 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 14 5; exact PV_CBM_InventoryShape.free_padding 14 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 15 5; exact PV_CBM_InventoryShape.free_padding 15 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 29 5; exact PV_CBM_InventoryShape.free_padding 29 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 30 5; exact PV_CBM_InventoryShape.free_padding 30 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 31 5; exact PV_CBM_InventoryShape.free_padding 31 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 45 5; exact PV_CBM_InventoryShape.free_padding 45 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 46 5; exact PV_CBM_InventoryShape.free_padding 46 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 47 5; exact PV_CBM_InventoryShape.free_padding 47 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 61 5; exact PV_CBM_InventoryShape.free_padding 61 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 62 5; exact PV_CBM_InventoryShape.free_padding 62 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 63 5; exact PV_CBM_InventoryShape.free_padding 63 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 77 5; exact PV_CBM_InventoryShape.free_padding 77 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 78 5; exact PV_CBM_InventoryShape.free_padding 78 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 79 5; exact PV_CBM_InventoryShape.free_padding 79 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 93 5; exact PV_CBM_InventoryShape.free_padding 93 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 94 5; exact PV_CBM_InventoryShape.free_padding 94 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 95 5; exact PV_CBM_InventoryShape.free_padding 95 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 109 5; exact PV_CBM_InventoryShape.free_padding 109 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 110 5; exact PV_CBM_InventoryShape.free_padding 110 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 111 5; exact PV_CBM_InventoryShape.free_padding 111 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 125 5; exact PV_CBM_InventoryShape.free_padding 125 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 126 5; exact PV_CBM_InventoryShape.free_padding 126 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 127 5; exact PV_CBM_InventoryShape.free_padding 127 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 141 5; exact PV_CBM_InventoryShape.free_padding 141 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 142 5; exact PV_CBM_InventoryShape.free_padding 142 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 143 5; exact PV_CBM_InventoryShape.free_padding 143 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 157 5; exact PV_CBM_InventoryShape.free_padding 157 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 158 5; exact PV_CBM_InventoryShape.free_padding 158 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 159 5; exact PV_CBM_InventoryShape.free_padding 159 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 173 5; exact PV_CBM_InventoryShape.free_padding 173 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 174 5; exact PV_CBM_InventoryShape.free_padding 174 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 175 5; exact PV_CBM_InventoryShape.free_padding 175 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 189 5; exact PV_CBM_InventoryShape.free_padding 189 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 190 5; exact PV_CBM_InventoryShape.free_padding 190 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 191 5; exact PV_CBM_InventoryShape.free_padding 191 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 205 5; exact PV_CBM_InventoryShape.free_padding 205 5 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk17
