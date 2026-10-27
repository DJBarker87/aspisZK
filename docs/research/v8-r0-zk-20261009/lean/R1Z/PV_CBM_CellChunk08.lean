-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_8]:
    Source: 'reference.rs', lines 831:0-896:1
    Visibility: public -/
def reference.cells_chunk_8
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 367#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 381#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 382#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 383#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 397#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 398#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 399#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 413#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 414#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 415#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 429#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 430#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 431#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 445#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 446#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 447#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 461#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 462#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 463#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 477#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 478#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 479#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 493#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 494#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 495#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 509#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 510#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 511#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 525#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 526#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 527#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 541#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 542#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 543#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 557#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 558#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 559#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 573#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 574#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 575#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 589#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 590#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 591#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 605#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 606#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 607#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 621#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 622#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 623#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 637#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 638#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 639#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 653#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 654#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 655#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 669#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 670#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 671#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 685#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 686#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 687#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 701#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 702#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 703#u16, column := 2#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk08
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 367#u16, column := 2#u8},
    {row := 381#u16, column := 2#u8},
    {row := 382#u16, column := 2#u8},
    {row := 383#u16, column := 2#u8},
    {row := 397#u16, column := 2#u8},
    {row := 398#u16, column := 2#u8},
    {row := 399#u16, column := 2#u8},
    {row := 413#u16, column := 2#u8},
    {row := 414#u16, column := 2#u8},
    {row := 415#u16, column := 2#u8},
    {row := 429#u16, column := 2#u8},
    {row := 430#u16, column := 2#u8},
    {row := 431#u16, column := 2#u8},
    {row := 445#u16, column := 2#u8},
    {row := 446#u16, column := 2#u8},
    {row := 447#u16, column := 2#u8},
    {row := 461#u16, column := 2#u8},
    {row := 462#u16, column := 2#u8},
    {row := 463#u16, column := 2#u8},
    {row := 477#u16, column := 2#u8},
    {row := 478#u16, column := 2#u8},
    {row := 479#u16, column := 2#u8},
    {row := 493#u16, column := 2#u8},
    {row := 494#u16, column := 2#u8},
    {row := 495#u16, column := 2#u8},
    {row := 509#u16, column := 2#u8},
    {row := 510#u16, column := 2#u8},
    {row := 511#u16, column := 2#u8},
    {row := 525#u16, column := 2#u8},
    {row := 526#u16, column := 2#u8},
    {row := 527#u16, column := 2#u8},
    {row := 541#u16, column := 2#u8},
    {row := 542#u16, column := 2#u8},
    {row := 543#u16, column := 2#u8},
    {row := 557#u16, column := 2#u8},
    {row := 558#u16, column := 2#u8},
    {row := 559#u16, column := 2#u8},
    {row := 573#u16, column := 2#u8},
    {row := 574#u16, column := 2#u8},
    {row := 575#u16, column := 2#u8},
    {row := 589#u16, column := 2#u8},
    {row := 590#u16, column := 2#u8},
    {row := 591#u16, column := 2#u8},
    {row := 605#u16, column := 2#u8},
    {row := 606#u16, column := 2#u8},
    {row := 607#u16, column := 2#u8},
    {row := 621#u16, column := 2#u8},
    {row := 622#u16, column := 2#u8},
    {row := 623#u16, column := 2#u8},
    {row := 637#u16, column := 2#u8},
    {row := 638#u16, column := 2#u8},
    {row := 639#u16, column := 2#u8},
    {row := 653#u16, column := 2#u8},
    {row := 654#u16, column := 2#u8},
    {row := 655#u16, column := 2#u8},
    {row := 669#u16, column := 2#u8},
    {row := 670#u16, column := 2#u8},
    {row := 671#u16, column := 2#u8},
    {row := 685#u16, column := 2#u8},
    {row := 686#u16, column := 2#u8},
    {row := 687#u16, column := 2#u8},
    {row := 701#u16, column := 2#u8},
    {row := 702#u16, column := 2#u8},
    {row := 703#u16, column := 2#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_8 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_8
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_8 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 367 2; exact PV_CBM_InventoryShape.free_padding 367 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 381 2; exact PV_CBM_InventoryShape.free_padding 381 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 382 2; exact PV_CBM_InventoryShape.free_padding 382 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 383 2; exact PV_CBM_InventoryShape.free_padding 383 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 397 2; exact PV_CBM_InventoryShape.free_padding 397 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 398 2; exact PV_CBM_InventoryShape.free_padding 398 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 399 2; exact PV_CBM_InventoryShape.free_padding 399 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 413 2; exact PV_CBM_InventoryShape.free_padding 413 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 414 2; exact PV_CBM_InventoryShape.free_padding 414 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 415 2; exact PV_CBM_InventoryShape.free_padding 415 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 429 2; exact PV_CBM_InventoryShape.free_padding 429 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 430 2; exact PV_CBM_InventoryShape.free_padding 430 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 431 2; exact PV_CBM_InventoryShape.free_padding 431 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 445 2; exact PV_CBM_InventoryShape.free_padding 445 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 446 2; exact PV_CBM_InventoryShape.free_padding 446 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 447 2; exact PV_CBM_InventoryShape.free_padding 447 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 461 2; exact PV_CBM_InventoryShape.free_padding 461 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 462 2; exact PV_CBM_InventoryShape.free_padding 462 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 463 2; exact PV_CBM_InventoryShape.free_padding 463 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 477 2; exact PV_CBM_InventoryShape.free_padding 477 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 478 2; exact PV_CBM_InventoryShape.free_padding 478 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 479 2; exact PV_CBM_InventoryShape.free_padding 479 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 493 2; exact PV_CBM_InventoryShape.free_padding 493 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 494 2; exact PV_CBM_InventoryShape.free_padding 494 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 495 2; exact PV_CBM_InventoryShape.free_padding 495 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 509 2; exact PV_CBM_InventoryShape.free_padding 509 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 510 2; exact PV_CBM_InventoryShape.free_padding 510 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 511 2; exact PV_CBM_InventoryShape.free_padding 511 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 525 2; exact PV_CBM_InventoryShape.free_padding 525 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 526 2; exact PV_CBM_InventoryShape.free_padding 526 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 527 2; exact PV_CBM_InventoryShape.free_padding 527 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 541 2; exact PV_CBM_InventoryShape.free_padding 541 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 542 2; exact PV_CBM_InventoryShape.free_padding 542 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 543 2; exact PV_CBM_InventoryShape.free_padding 543 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 557 2; exact PV_CBM_InventoryShape.free_padding 557 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 558 2; exact PV_CBM_InventoryShape.free_padding 558 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 559 2; exact PV_CBM_InventoryShape.free_padding 559 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 573 2; exact PV_CBM_InventoryShape.free_padding 573 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 574 2; exact PV_CBM_InventoryShape.free_padding 574 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 575 2; exact PV_CBM_InventoryShape.free_padding 575 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 589 2; exact PV_CBM_InventoryShape.free_padding 589 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 590 2; exact PV_CBM_InventoryShape.free_padding 590 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 591 2; exact PV_CBM_InventoryShape.free_padding 591 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 605 2; exact PV_CBM_InventoryShape.free_padding 605 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 606 2; exact PV_CBM_InventoryShape.free_padding 606 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 607 2; exact PV_CBM_InventoryShape.free_padding 607 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 621 2; exact PV_CBM_InventoryShape.free_padding 621 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 622 2; exact PV_CBM_InventoryShape.free_padding 622 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 623 2; exact PV_CBM_InventoryShape.free_padding 623 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 637 2; exact PV_CBM_InventoryShape.free_padding 637 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 638 2; exact PV_CBM_InventoryShape.free_padding 638 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 639 2; exact PV_CBM_InventoryShape.free_padding 639 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 653 2; exact PV_CBM_InventoryShape.free_padding 653 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 654 2; exact PV_CBM_InventoryShape.free_padding 654 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 655 2; exact PV_CBM_InventoryShape.free_padding 655 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 669 2; exact PV_CBM_InventoryShape.free_padding 669 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 670 2; exact PV_CBM_InventoryShape.free_padding 670 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 671 2; exact PV_CBM_InventoryShape.free_padding 671 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 685 2; exact PV_CBM_InventoryShape.free_padding 685 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 686 2; exact PV_CBM_InventoryShape.free_padding 686 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 687 2; exact PV_CBM_InventoryShape.free_padding 687 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 701 2; exact PV_CBM_InventoryShape.free_padding 701 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 702 2; exact PV_CBM_InventoryShape.free_padding 702 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 703 2; exact PV_CBM_InventoryShape.free_padding 703 2 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk08
