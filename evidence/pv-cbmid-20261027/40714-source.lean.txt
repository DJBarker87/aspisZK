-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_48]:
    Source: 'reference.rs', lines 3471:0-3536:1
    Visibility: public -/
def reference.cells_chunk_48
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 254#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 255#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 269#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 270#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 271#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 285#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 286#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 287#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 301#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 302#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 303#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 317#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 318#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 319#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 333#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 334#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 335#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 349#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 350#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 351#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 365#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 366#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 367#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 381#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 382#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 383#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 397#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 398#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 399#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 413#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 414#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 415#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 429#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 430#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 431#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 445#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 446#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 447#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 461#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 462#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 463#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 477#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 478#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 479#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 493#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 494#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 495#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 509#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 510#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 511#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 525#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 526#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 527#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 541#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 542#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 543#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 557#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 558#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 559#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 573#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 574#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 575#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 589#u16, column := 13#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 590#u16, column := 13#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk48
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 254#u16, column := 13#u8},
    {row := 255#u16, column := 13#u8},
    {row := 269#u16, column := 13#u8},
    {row := 270#u16, column := 13#u8},
    {row := 271#u16, column := 13#u8},
    {row := 285#u16, column := 13#u8},
    {row := 286#u16, column := 13#u8},
    {row := 287#u16, column := 13#u8},
    {row := 301#u16, column := 13#u8},
    {row := 302#u16, column := 13#u8},
    {row := 303#u16, column := 13#u8},
    {row := 317#u16, column := 13#u8},
    {row := 318#u16, column := 13#u8},
    {row := 319#u16, column := 13#u8},
    {row := 333#u16, column := 13#u8},
    {row := 334#u16, column := 13#u8},
    {row := 335#u16, column := 13#u8},
    {row := 349#u16, column := 13#u8},
    {row := 350#u16, column := 13#u8},
    {row := 351#u16, column := 13#u8},
    {row := 365#u16, column := 13#u8},
    {row := 366#u16, column := 13#u8},
    {row := 367#u16, column := 13#u8},
    {row := 381#u16, column := 13#u8},
    {row := 382#u16, column := 13#u8},
    {row := 383#u16, column := 13#u8},
    {row := 397#u16, column := 13#u8},
    {row := 398#u16, column := 13#u8},
    {row := 399#u16, column := 13#u8},
    {row := 413#u16, column := 13#u8},
    {row := 414#u16, column := 13#u8},
    {row := 415#u16, column := 13#u8},
    {row := 429#u16, column := 13#u8},
    {row := 430#u16, column := 13#u8},
    {row := 431#u16, column := 13#u8},
    {row := 445#u16, column := 13#u8},
    {row := 446#u16, column := 13#u8},
    {row := 447#u16, column := 13#u8},
    {row := 461#u16, column := 13#u8},
    {row := 462#u16, column := 13#u8},
    {row := 463#u16, column := 13#u8},
    {row := 477#u16, column := 13#u8},
    {row := 478#u16, column := 13#u8},
    {row := 479#u16, column := 13#u8},
    {row := 493#u16, column := 13#u8},
    {row := 494#u16, column := 13#u8},
    {row := 495#u16, column := 13#u8},
    {row := 509#u16, column := 13#u8},
    {row := 510#u16, column := 13#u8},
    {row := 511#u16, column := 13#u8},
    {row := 525#u16, column := 13#u8},
    {row := 526#u16, column := 13#u8},
    {row := 527#u16, column := 13#u8},
    {row := 541#u16, column := 13#u8},
    {row := 542#u16, column := 13#u8},
    {row := 543#u16, column := 13#u8},
    {row := 557#u16, column := 13#u8},
    {row := 558#u16, column := 13#u8},
    {row := 559#u16, column := 13#u8},
    {row := 573#u16, column := 13#u8},
    {row := 574#u16, column := 13#u8},
    {row := 575#u16, column := 13#u8},
    {row := 589#u16, column := 13#u8},
    {row := 590#u16, column := 13#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_48 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_48
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_48 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 254 13; exact PV_CBM_InventoryShape.free_padding 254 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 255 13; exact PV_CBM_InventoryShape.free_padding 255 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 269 13; exact PV_CBM_InventoryShape.free_padding 269 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 270 13; exact PV_CBM_InventoryShape.free_padding 270 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 271 13; exact PV_CBM_InventoryShape.free_padding 271 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 285 13; exact PV_CBM_InventoryShape.free_padding 285 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 286 13; exact PV_CBM_InventoryShape.free_padding 286 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 287 13; exact PV_CBM_InventoryShape.free_padding 287 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 301 13; exact PV_CBM_InventoryShape.free_padding 301 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 302 13; exact PV_CBM_InventoryShape.free_padding 302 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 303 13; exact PV_CBM_InventoryShape.free_padding 303 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 317 13; exact PV_CBM_InventoryShape.free_padding 317 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 318 13; exact PV_CBM_InventoryShape.free_padding 318 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 319 13; exact PV_CBM_InventoryShape.free_padding 319 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 333 13; exact PV_CBM_InventoryShape.free_padding 333 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 334 13; exact PV_CBM_InventoryShape.free_padding 334 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 335 13; exact PV_CBM_InventoryShape.free_padding 335 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 349 13; exact PV_CBM_InventoryShape.free_padding 349 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 350 13; exact PV_CBM_InventoryShape.free_padding 350 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 351 13; exact PV_CBM_InventoryShape.free_padding 351 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 365 13; exact PV_CBM_InventoryShape.free_padding 365 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 366 13; exact PV_CBM_InventoryShape.free_padding 366 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 367 13; exact PV_CBM_InventoryShape.free_padding 367 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 381 13; exact PV_CBM_InventoryShape.free_padding 381 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 382 13; exact PV_CBM_InventoryShape.free_padding 382 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 383 13; exact PV_CBM_InventoryShape.free_padding 383 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 397 13; exact PV_CBM_InventoryShape.free_padding 397 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 398 13; exact PV_CBM_InventoryShape.free_padding 398 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 399 13; exact PV_CBM_InventoryShape.free_padding 399 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 413 13; exact PV_CBM_InventoryShape.free_padding 413 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 414 13; exact PV_CBM_InventoryShape.free_padding 414 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 415 13; exact PV_CBM_InventoryShape.free_padding 415 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 429 13; exact PV_CBM_InventoryShape.free_padding 429 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 430 13; exact PV_CBM_InventoryShape.free_padding 430 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 431 13; exact PV_CBM_InventoryShape.free_padding 431 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 445 13; exact PV_CBM_InventoryShape.free_padding 445 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 446 13; exact PV_CBM_InventoryShape.free_padding 446 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 447 13; exact PV_CBM_InventoryShape.free_padding 447 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 461 13; exact PV_CBM_InventoryShape.free_padding 461 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 462 13; exact PV_CBM_InventoryShape.free_padding 462 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 463 13; exact PV_CBM_InventoryShape.free_padding 463 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 477 13; exact PV_CBM_InventoryShape.free_padding 477 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 478 13; exact PV_CBM_InventoryShape.free_padding 478 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 479 13; exact PV_CBM_InventoryShape.free_padding 479 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 493 13; exact PV_CBM_InventoryShape.free_padding 493 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 494 13; exact PV_CBM_InventoryShape.free_padding 494 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 495 13; exact PV_CBM_InventoryShape.free_padding 495 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 509 13; exact PV_CBM_InventoryShape.free_padding 509 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 510 13; exact PV_CBM_InventoryShape.free_padding 510 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 511 13; exact PV_CBM_InventoryShape.free_padding 511 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 525 13; exact PV_CBM_InventoryShape.free_padding 525 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 526 13; exact PV_CBM_InventoryShape.free_padding 526 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 527 13; exact PV_CBM_InventoryShape.free_padding 527 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 541 13; exact PV_CBM_InventoryShape.free_padding 541 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 542 13; exact PV_CBM_InventoryShape.free_padding 542 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 543 13; exact PV_CBM_InventoryShape.free_padding 543 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 557 13; exact PV_CBM_InventoryShape.free_padding 557 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 558 13; exact PV_CBM_InventoryShape.free_padding 558 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 559 13; exact PV_CBM_InventoryShape.free_padding 559 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 573 13; exact PV_CBM_InventoryShape.free_padding 573 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 574 13; exact PV_CBM_InventoryShape.free_padding 574 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 575 13; exact PV_CBM_InventoryShape.free_padding 575 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 589 13; exact PV_CBM_InventoryShape.free_padding 589 13 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 590 13; exact PV_CBM_InventoryShape.free_padding 590 13 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk48
