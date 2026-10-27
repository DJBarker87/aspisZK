-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_19]:
    Source: 'reference.rs', lines 1557:0-1622:1
    Visibility: public -/
def reference.cells_chunk_19
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 543#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 557#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 558#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 559#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 573#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 574#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 575#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 589#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 590#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 591#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 605#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 606#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 607#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 621#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 622#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 623#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 637#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 638#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 639#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 653#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 654#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 655#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 669#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 670#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 671#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 685#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 686#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 687#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 701#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 702#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 703#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 717#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 718#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 719#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 733#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 734#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 735#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 749#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 750#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 751#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 765#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 766#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 767#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 781#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 782#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 783#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 797#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 798#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 799#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 813#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 814#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 815#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 829#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 830#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 831#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 845#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 846#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 847#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 861#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 862#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 863#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 877#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 878#u16, column := 5#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 879#u16, column := 5#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk19
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 543#u16, column := 5#u8},
    {row := 557#u16, column := 5#u8},
    {row := 558#u16, column := 5#u8},
    {row := 559#u16, column := 5#u8},
    {row := 573#u16, column := 5#u8},
    {row := 574#u16, column := 5#u8},
    {row := 575#u16, column := 5#u8},
    {row := 589#u16, column := 5#u8},
    {row := 590#u16, column := 5#u8},
    {row := 591#u16, column := 5#u8},
    {row := 605#u16, column := 5#u8},
    {row := 606#u16, column := 5#u8},
    {row := 607#u16, column := 5#u8},
    {row := 621#u16, column := 5#u8},
    {row := 622#u16, column := 5#u8},
    {row := 623#u16, column := 5#u8},
    {row := 637#u16, column := 5#u8},
    {row := 638#u16, column := 5#u8},
    {row := 639#u16, column := 5#u8},
    {row := 653#u16, column := 5#u8},
    {row := 654#u16, column := 5#u8},
    {row := 655#u16, column := 5#u8},
    {row := 669#u16, column := 5#u8},
    {row := 670#u16, column := 5#u8},
    {row := 671#u16, column := 5#u8},
    {row := 685#u16, column := 5#u8},
    {row := 686#u16, column := 5#u8},
    {row := 687#u16, column := 5#u8},
    {row := 701#u16, column := 5#u8},
    {row := 702#u16, column := 5#u8},
    {row := 703#u16, column := 5#u8},
    {row := 717#u16, column := 5#u8},
    {row := 718#u16, column := 5#u8},
    {row := 719#u16, column := 5#u8},
    {row := 733#u16, column := 5#u8},
    {row := 734#u16, column := 5#u8},
    {row := 735#u16, column := 5#u8},
    {row := 749#u16, column := 5#u8},
    {row := 750#u16, column := 5#u8},
    {row := 751#u16, column := 5#u8},
    {row := 765#u16, column := 5#u8},
    {row := 766#u16, column := 5#u8},
    {row := 767#u16, column := 5#u8},
    {row := 781#u16, column := 5#u8},
    {row := 782#u16, column := 5#u8},
    {row := 783#u16, column := 5#u8},
    {row := 797#u16, column := 5#u8},
    {row := 798#u16, column := 5#u8},
    {row := 799#u16, column := 5#u8},
    {row := 813#u16, column := 5#u8},
    {row := 814#u16, column := 5#u8},
    {row := 815#u16, column := 5#u8},
    {row := 829#u16, column := 5#u8},
    {row := 830#u16, column := 5#u8},
    {row := 831#u16, column := 5#u8},
    {row := 845#u16, column := 5#u8},
    {row := 846#u16, column := 5#u8},
    {row := 847#u16, column := 5#u8},
    {row := 861#u16, column := 5#u8},
    {row := 862#u16, column := 5#u8},
    {row := 863#u16, column := 5#u8},
    {row := 877#u16, column := 5#u8},
    {row := 878#u16, column := 5#u8},
    {row := 879#u16, column := 5#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_19 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_19
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_19 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 543 5; exact PV_CBM_InventoryShape.free_padding 543 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 557 5; exact PV_CBM_InventoryShape.free_padding 557 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 558 5; exact PV_CBM_InventoryShape.free_padding 558 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 559 5; exact PV_CBM_InventoryShape.free_padding 559 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 573 5; exact PV_CBM_InventoryShape.free_padding 573 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 574 5; exact PV_CBM_InventoryShape.free_padding 574 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 575 5; exact PV_CBM_InventoryShape.free_padding 575 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 589 5; exact PV_CBM_InventoryShape.free_padding 589 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 590 5; exact PV_CBM_InventoryShape.free_padding 590 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 591 5; exact PV_CBM_InventoryShape.free_padding 591 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 605 5; exact PV_CBM_InventoryShape.free_padding 605 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 606 5; exact PV_CBM_InventoryShape.free_padding 606 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 607 5; exact PV_CBM_InventoryShape.free_padding 607 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 621 5; exact PV_CBM_InventoryShape.free_padding 621 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 622 5; exact PV_CBM_InventoryShape.free_padding 622 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 623 5; exact PV_CBM_InventoryShape.free_padding 623 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 637 5; exact PV_CBM_InventoryShape.free_padding 637 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 638 5; exact PV_CBM_InventoryShape.free_padding 638 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 639 5; exact PV_CBM_InventoryShape.free_padding 639 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 653 5; exact PV_CBM_InventoryShape.free_padding 653 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 654 5; exact PV_CBM_InventoryShape.free_padding 654 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 655 5; exact PV_CBM_InventoryShape.free_padding 655 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 669 5; exact PV_CBM_InventoryShape.free_padding 669 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 670 5; exact PV_CBM_InventoryShape.free_padding 670 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 671 5; exact PV_CBM_InventoryShape.free_padding 671 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 685 5; exact PV_CBM_InventoryShape.free_padding 685 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 686 5; exact PV_CBM_InventoryShape.free_padding 686 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 687 5; exact PV_CBM_InventoryShape.free_padding 687 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 701 5; exact PV_CBM_InventoryShape.free_padding 701 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 702 5; exact PV_CBM_InventoryShape.free_padding 702 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 703 5; exact PV_CBM_InventoryShape.free_padding 703 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 717 5; exact PV_CBM_InventoryShape.free_padding 717 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 718 5; exact PV_CBM_InventoryShape.free_padding 718 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 719 5; exact PV_CBM_InventoryShape.free_padding 719 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 733 5; exact PV_CBM_InventoryShape.free_padding 733 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 734 5; exact PV_CBM_InventoryShape.free_padding 734 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 735 5; exact PV_CBM_InventoryShape.free_padding 735 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 749 5; exact PV_CBM_InventoryShape.free_padding 749 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 750 5; exact PV_CBM_InventoryShape.free_padding 750 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 751 5; exact PV_CBM_InventoryShape.free_padding 751 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 765 5; exact PV_CBM_InventoryShape.free_padding 765 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 766 5; exact PV_CBM_InventoryShape.free_padding 766 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 767 5; exact PV_CBM_InventoryShape.free_padding 767 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 781 5; exact PV_CBM_InventoryShape.free_padding 781 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 782 5; exact PV_CBM_InventoryShape.free_padding 782 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 783 5; exact PV_CBM_InventoryShape.free_padding 783 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 797 5; exact PV_CBM_InventoryShape.free_padding 797 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 798 5; exact PV_CBM_InventoryShape.free_padding 798 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 799 5; exact PV_CBM_InventoryShape.free_padding 799 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 813 5; exact PV_CBM_InventoryShape.free_padding 813 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 814 5; exact PV_CBM_InventoryShape.free_padding 814 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 815 5; exact PV_CBM_InventoryShape.free_padding 815 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 829 5; exact PV_CBM_InventoryShape.free_padding 829 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 830 5; exact PV_CBM_InventoryShape.free_padding 830 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 831 5; exact PV_CBM_InventoryShape.free_padding 831 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 845 5; exact PV_CBM_InventoryShape.free_padding 845 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 846 5; exact PV_CBM_InventoryShape.free_padding 846 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 847 5; exact PV_CBM_InventoryShape.free_padding 847 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 861 5; exact PV_CBM_InventoryShape.free_padding 861 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 862 5; exact PV_CBM_InventoryShape.free_padding 862 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 863 5; exact PV_CBM_InventoryShape.free_padding 863 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 877 5; exact PV_CBM_InventoryShape.free_padding 877 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 878 5; exact PV_CBM_InventoryShape.free_padding 878 5 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 879 5; exact PV_CBM_InventoryShape.free_padding 879 5 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk19
