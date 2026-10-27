-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_29]:
    Source: 'reference.rs', lines 2217:0-2282:1
    Visibility: public -/
def reference.cells_chunk_29
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 381#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 382#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 383#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 397#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 398#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 399#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 413#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 414#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 415#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 429#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 430#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 431#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 445#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 446#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 447#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 461#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 462#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 463#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 477#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 478#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 479#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 493#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 494#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 495#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 509#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 510#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 511#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 525#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 526#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 527#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 541#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 542#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 543#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 557#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 558#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 559#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 573#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 574#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 575#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 589#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 590#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 591#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 605#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 606#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 607#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 621#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 622#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 623#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 637#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 638#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 639#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 653#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 654#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 655#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 669#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 670#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 671#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 685#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 686#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 687#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 701#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 702#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 703#u16, column := 8#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 717#u16, column := 8#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk29
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 381#u16, column := 8#u8},
    {row := 382#u16, column := 8#u8},
    {row := 383#u16, column := 8#u8},
    {row := 397#u16, column := 8#u8},
    {row := 398#u16, column := 8#u8},
    {row := 399#u16, column := 8#u8},
    {row := 413#u16, column := 8#u8},
    {row := 414#u16, column := 8#u8},
    {row := 415#u16, column := 8#u8},
    {row := 429#u16, column := 8#u8},
    {row := 430#u16, column := 8#u8},
    {row := 431#u16, column := 8#u8},
    {row := 445#u16, column := 8#u8},
    {row := 446#u16, column := 8#u8},
    {row := 447#u16, column := 8#u8},
    {row := 461#u16, column := 8#u8},
    {row := 462#u16, column := 8#u8},
    {row := 463#u16, column := 8#u8},
    {row := 477#u16, column := 8#u8},
    {row := 478#u16, column := 8#u8},
    {row := 479#u16, column := 8#u8},
    {row := 493#u16, column := 8#u8},
    {row := 494#u16, column := 8#u8},
    {row := 495#u16, column := 8#u8},
    {row := 509#u16, column := 8#u8},
    {row := 510#u16, column := 8#u8},
    {row := 511#u16, column := 8#u8},
    {row := 525#u16, column := 8#u8},
    {row := 526#u16, column := 8#u8},
    {row := 527#u16, column := 8#u8},
    {row := 541#u16, column := 8#u8},
    {row := 542#u16, column := 8#u8},
    {row := 543#u16, column := 8#u8},
    {row := 557#u16, column := 8#u8},
    {row := 558#u16, column := 8#u8},
    {row := 559#u16, column := 8#u8},
    {row := 573#u16, column := 8#u8},
    {row := 574#u16, column := 8#u8},
    {row := 575#u16, column := 8#u8},
    {row := 589#u16, column := 8#u8},
    {row := 590#u16, column := 8#u8},
    {row := 591#u16, column := 8#u8},
    {row := 605#u16, column := 8#u8},
    {row := 606#u16, column := 8#u8},
    {row := 607#u16, column := 8#u8},
    {row := 621#u16, column := 8#u8},
    {row := 622#u16, column := 8#u8},
    {row := 623#u16, column := 8#u8},
    {row := 637#u16, column := 8#u8},
    {row := 638#u16, column := 8#u8},
    {row := 639#u16, column := 8#u8},
    {row := 653#u16, column := 8#u8},
    {row := 654#u16, column := 8#u8},
    {row := 655#u16, column := 8#u8},
    {row := 669#u16, column := 8#u8},
    {row := 670#u16, column := 8#u8},
    {row := 671#u16, column := 8#u8},
    {row := 685#u16, column := 8#u8},
    {row := 686#u16, column := 8#u8},
    {row := 687#u16, column := 8#u8},
    {row := 701#u16, column := 8#u8},
    {row := 702#u16, column := 8#u8},
    {row := 703#u16, column := 8#u8},
    {row := 717#u16, column := 8#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_29 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_29
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_29 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 381 8; exact PV_CBM_InventoryShape.free_padding 381 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 382 8; exact PV_CBM_InventoryShape.free_padding 382 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 383 8; exact PV_CBM_InventoryShape.free_padding 383 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 397 8; exact PV_CBM_InventoryShape.free_padding 397 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 398 8; exact PV_CBM_InventoryShape.free_padding 398 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 399 8; exact PV_CBM_InventoryShape.free_padding 399 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 413 8; exact PV_CBM_InventoryShape.free_padding 413 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 414 8; exact PV_CBM_InventoryShape.free_padding 414 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 415 8; exact PV_CBM_InventoryShape.free_padding 415 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 429 8; exact PV_CBM_InventoryShape.free_padding 429 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 430 8; exact PV_CBM_InventoryShape.free_padding 430 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 431 8; exact PV_CBM_InventoryShape.free_padding 431 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 445 8; exact PV_CBM_InventoryShape.free_padding 445 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 446 8; exact PV_CBM_InventoryShape.free_padding 446 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 447 8; exact PV_CBM_InventoryShape.free_padding 447 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 461 8; exact PV_CBM_InventoryShape.free_padding 461 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 462 8; exact PV_CBM_InventoryShape.free_padding 462 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 463 8; exact PV_CBM_InventoryShape.free_padding 463 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 477 8; exact PV_CBM_InventoryShape.free_padding 477 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 478 8; exact PV_CBM_InventoryShape.free_padding 478 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 479 8; exact PV_CBM_InventoryShape.free_padding 479 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 493 8; exact PV_CBM_InventoryShape.free_padding 493 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 494 8; exact PV_CBM_InventoryShape.free_padding 494 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 495 8; exact PV_CBM_InventoryShape.free_padding 495 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 509 8; exact PV_CBM_InventoryShape.free_padding 509 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 510 8; exact PV_CBM_InventoryShape.free_padding 510 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 511 8; exact PV_CBM_InventoryShape.free_padding 511 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 525 8; exact PV_CBM_InventoryShape.free_padding 525 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 526 8; exact PV_CBM_InventoryShape.free_padding 526 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 527 8; exact PV_CBM_InventoryShape.free_padding 527 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 541 8; exact PV_CBM_InventoryShape.free_padding 541 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 542 8; exact PV_CBM_InventoryShape.free_padding 542 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 543 8; exact PV_CBM_InventoryShape.free_padding 543 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 557 8; exact PV_CBM_InventoryShape.free_padding 557 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 558 8; exact PV_CBM_InventoryShape.free_padding 558 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 559 8; exact PV_CBM_InventoryShape.free_padding 559 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 573 8; exact PV_CBM_InventoryShape.free_padding 573 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 574 8; exact PV_CBM_InventoryShape.free_padding 574 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 575 8; exact PV_CBM_InventoryShape.free_padding 575 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 589 8; exact PV_CBM_InventoryShape.free_padding 589 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 590 8; exact PV_CBM_InventoryShape.free_padding 590 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 591 8; exact PV_CBM_InventoryShape.free_padding 591 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 605 8; exact PV_CBM_InventoryShape.free_padding 605 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 606 8; exact PV_CBM_InventoryShape.free_padding 606 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 607 8; exact PV_CBM_InventoryShape.free_padding 607 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 621 8; exact PV_CBM_InventoryShape.free_padding 621 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 622 8; exact PV_CBM_InventoryShape.free_padding 622 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 623 8; exact PV_CBM_InventoryShape.free_padding 623 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 637 8; exact PV_CBM_InventoryShape.free_padding 637 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 638 8; exact PV_CBM_InventoryShape.free_padding 638 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 639 8; exact PV_CBM_InventoryShape.free_padding 639 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 653 8; exact PV_CBM_InventoryShape.free_padding 653 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 654 8; exact PV_CBM_InventoryShape.free_padding 654 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 655 8; exact PV_CBM_InventoryShape.free_padding 655 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 669 8; exact PV_CBM_InventoryShape.free_padding 669 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 670 8; exact PV_CBM_InventoryShape.free_padding 670 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 671 8; exact PV_CBM_InventoryShape.free_padding 671 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 685 8; exact PV_CBM_InventoryShape.free_padding 685 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 686 8; exact PV_CBM_InventoryShape.free_padding 686 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 687 8; exact PV_CBM_InventoryShape.free_padding 687 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 701 8; exact PV_CBM_InventoryShape.free_padding 701 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 702 8; exact PV_CBM_InventoryShape.free_padding 702 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 703 8; exact PV_CBM_InventoryShape.free_padding 703 8 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 717 8; exact PV_CBM_InventoryShape.free_padding 717 8 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk29
