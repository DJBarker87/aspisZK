-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_7]:
    Source: 'reference.rs', lines 765:0-830:1
    Visibility: public -/
def reference.cells_chunk_7
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 30#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 31#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 45#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 46#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 47#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 61#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 62#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 63#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 77#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 78#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 79#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 93#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 94#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 95#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 109#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 110#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 111#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 125#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 126#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 127#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 141#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 142#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 143#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 157#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 158#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 159#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 173#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 174#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 175#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 189#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 190#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 191#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 205#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 206#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 207#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 221#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 222#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 223#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 237#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 238#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 239#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 253#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 254#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 255#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 269#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 270#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 271#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 285#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 286#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 287#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 301#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 302#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 303#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 317#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 318#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 319#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 333#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 334#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 335#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 349#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 350#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 351#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 365#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 366#u16, column := 2#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk07
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 30#u16, column := 2#u8},
    {row := 31#u16, column := 2#u8},
    {row := 45#u16, column := 2#u8},
    {row := 46#u16, column := 2#u8},
    {row := 47#u16, column := 2#u8},
    {row := 61#u16, column := 2#u8},
    {row := 62#u16, column := 2#u8},
    {row := 63#u16, column := 2#u8},
    {row := 77#u16, column := 2#u8},
    {row := 78#u16, column := 2#u8},
    {row := 79#u16, column := 2#u8},
    {row := 93#u16, column := 2#u8},
    {row := 94#u16, column := 2#u8},
    {row := 95#u16, column := 2#u8},
    {row := 109#u16, column := 2#u8},
    {row := 110#u16, column := 2#u8},
    {row := 111#u16, column := 2#u8},
    {row := 125#u16, column := 2#u8},
    {row := 126#u16, column := 2#u8},
    {row := 127#u16, column := 2#u8},
    {row := 141#u16, column := 2#u8},
    {row := 142#u16, column := 2#u8},
    {row := 143#u16, column := 2#u8},
    {row := 157#u16, column := 2#u8},
    {row := 158#u16, column := 2#u8},
    {row := 159#u16, column := 2#u8},
    {row := 173#u16, column := 2#u8},
    {row := 174#u16, column := 2#u8},
    {row := 175#u16, column := 2#u8},
    {row := 189#u16, column := 2#u8},
    {row := 190#u16, column := 2#u8},
    {row := 191#u16, column := 2#u8},
    {row := 205#u16, column := 2#u8},
    {row := 206#u16, column := 2#u8},
    {row := 207#u16, column := 2#u8},
    {row := 221#u16, column := 2#u8},
    {row := 222#u16, column := 2#u8},
    {row := 223#u16, column := 2#u8},
    {row := 237#u16, column := 2#u8},
    {row := 238#u16, column := 2#u8},
    {row := 239#u16, column := 2#u8},
    {row := 253#u16, column := 2#u8},
    {row := 254#u16, column := 2#u8},
    {row := 255#u16, column := 2#u8},
    {row := 269#u16, column := 2#u8},
    {row := 270#u16, column := 2#u8},
    {row := 271#u16, column := 2#u8},
    {row := 285#u16, column := 2#u8},
    {row := 286#u16, column := 2#u8},
    {row := 287#u16, column := 2#u8},
    {row := 301#u16, column := 2#u8},
    {row := 302#u16, column := 2#u8},
    {row := 303#u16, column := 2#u8},
    {row := 317#u16, column := 2#u8},
    {row := 318#u16, column := 2#u8},
    {row := 319#u16, column := 2#u8},
    {row := 333#u16, column := 2#u8},
    {row := 334#u16, column := 2#u8},
    {row := 335#u16, column := 2#u8},
    {row := 349#u16, column := 2#u8},
    {row := 350#u16, column := 2#u8},
    {row := 351#u16, column := 2#u8},
    {row := 365#u16, column := 2#u8},
    {row := 366#u16, column := 2#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_7 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_7
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_7 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 30 2; exact PV_CBM_InventoryShape.free_padding 30 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 31 2; exact PV_CBM_InventoryShape.free_padding 31 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 45 2; exact PV_CBM_InventoryShape.free_padding 45 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 46 2; exact PV_CBM_InventoryShape.free_padding 46 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 47 2; exact PV_CBM_InventoryShape.free_padding 47 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 61 2; exact PV_CBM_InventoryShape.free_padding 61 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 62 2; exact PV_CBM_InventoryShape.free_padding 62 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 63 2; exact PV_CBM_InventoryShape.free_padding 63 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 77 2; exact PV_CBM_InventoryShape.free_padding 77 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 78 2; exact PV_CBM_InventoryShape.free_padding 78 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 79 2; exact PV_CBM_InventoryShape.free_padding 79 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 93 2; exact PV_CBM_InventoryShape.free_padding 93 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 94 2; exact PV_CBM_InventoryShape.free_padding 94 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 95 2; exact PV_CBM_InventoryShape.free_padding 95 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 109 2; exact PV_CBM_InventoryShape.free_padding 109 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 110 2; exact PV_CBM_InventoryShape.free_padding 110 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 111 2; exact PV_CBM_InventoryShape.free_padding 111 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 125 2; exact PV_CBM_InventoryShape.free_padding 125 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 126 2; exact PV_CBM_InventoryShape.free_padding 126 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 127 2; exact PV_CBM_InventoryShape.free_padding 127 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 141 2; exact PV_CBM_InventoryShape.free_padding 141 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 142 2; exact PV_CBM_InventoryShape.free_padding 142 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 143 2; exact PV_CBM_InventoryShape.free_padding 143 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 157 2; exact PV_CBM_InventoryShape.free_padding 157 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 158 2; exact PV_CBM_InventoryShape.free_padding 158 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 159 2; exact PV_CBM_InventoryShape.free_padding 159 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 173 2; exact PV_CBM_InventoryShape.free_padding 173 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 174 2; exact PV_CBM_InventoryShape.free_padding 174 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 175 2; exact PV_CBM_InventoryShape.free_padding 175 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 189 2; exact PV_CBM_InventoryShape.free_padding 189 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 190 2; exact PV_CBM_InventoryShape.free_padding 190 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 191 2; exact PV_CBM_InventoryShape.free_padding 191 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 205 2; exact PV_CBM_InventoryShape.free_padding 205 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 206 2; exact PV_CBM_InventoryShape.free_padding 206 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 207 2; exact PV_CBM_InventoryShape.free_padding 207 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 221 2; exact PV_CBM_InventoryShape.free_padding 221 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 222 2; exact PV_CBM_InventoryShape.free_padding 222 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 223 2; exact PV_CBM_InventoryShape.free_padding 223 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 237 2; exact PV_CBM_InventoryShape.free_padding 237 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 238 2; exact PV_CBM_InventoryShape.free_padding 238 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 239 2; exact PV_CBM_InventoryShape.free_padding 239 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 253 2; exact PV_CBM_InventoryShape.free_padding 253 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 254 2; exact PV_CBM_InventoryShape.free_padding 254 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 255 2; exact PV_CBM_InventoryShape.free_padding 255 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 269 2; exact PV_CBM_InventoryShape.free_padding 269 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 270 2; exact PV_CBM_InventoryShape.free_padding 270 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 271 2; exact PV_CBM_InventoryShape.free_padding 271 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 285 2; exact PV_CBM_InventoryShape.free_padding 285 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 286 2; exact PV_CBM_InventoryShape.free_padding 286 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 287 2; exact PV_CBM_InventoryShape.free_padding 287 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 301 2; exact PV_CBM_InventoryShape.free_padding 301 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 302 2; exact PV_CBM_InventoryShape.free_padding 302 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 303 2; exact PV_CBM_InventoryShape.free_padding 303 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 317 2; exact PV_CBM_InventoryShape.free_padding 317 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 318 2; exact PV_CBM_InventoryShape.free_padding 318 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 319 2; exact PV_CBM_InventoryShape.free_padding 319 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 333 2; exact PV_CBM_InventoryShape.free_padding 333 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 334 2; exact PV_CBM_InventoryShape.free_padding 334 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 335 2; exact PV_CBM_InventoryShape.free_padding 335 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 349 2; exact PV_CBM_InventoryShape.free_padding 349 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 350 2; exact PV_CBM_InventoryShape.free_padding 350 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 351 2; exact PV_CBM_InventoryShape.free_padding 351 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 365 2; exact PV_CBM_InventoryShape.free_padding 365 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 366 2; exact PV_CBM_InventoryShape.free_padding 366 2 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk07
