-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_16]:
    Source: 'reference.rs', lines 1359:0-1424:1
    Visibility: public -/
def reference.cells_chunk_16
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 718#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 719#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 733#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 734#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 735#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 749#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 750#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 751#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 765#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 766#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 767#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 781#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 782#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 783#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 797#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 798#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 799#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 813#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 814#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 815#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 829#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 830#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 831#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 845#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 846#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 847#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 861#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 862#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 863#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 877#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 878#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 879#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 893#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 894#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 895#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 909#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 910#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 911#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 912#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 915#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 916#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 919#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 920#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 923#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 924#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 927#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 928#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 931#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 932#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 935#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 936#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 939#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 940#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 943#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 944#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 947#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 948#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 951#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 952#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 955#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 956#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 959#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 960#u16, column := 4#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 963#u16, column := 4#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk16
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 718#u16, column := 4#u8},
    {row := 719#u16, column := 4#u8},
    {row := 733#u16, column := 4#u8},
    {row := 734#u16, column := 4#u8},
    {row := 735#u16, column := 4#u8},
    {row := 749#u16, column := 4#u8},
    {row := 750#u16, column := 4#u8},
    {row := 751#u16, column := 4#u8},
    {row := 765#u16, column := 4#u8},
    {row := 766#u16, column := 4#u8},
    {row := 767#u16, column := 4#u8},
    {row := 781#u16, column := 4#u8},
    {row := 782#u16, column := 4#u8},
    {row := 783#u16, column := 4#u8},
    {row := 797#u16, column := 4#u8},
    {row := 798#u16, column := 4#u8},
    {row := 799#u16, column := 4#u8},
    {row := 813#u16, column := 4#u8},
    {row := 814#u16, column := 4#u8},
    {row := 815#u16, column := 4#u8},
    {row := 829#u16, column := 4#u8},
    {row := 830#u16, column := 4#u8},
    {row := 831#u16, column := 4#u8},
    {row := 845#u16, column := 4#u8},
    {row := 846#u16, column := 4#u8},
    {row := 847#u16, column := 4#u8},
    {row := 861#u16, column := 4#u8},
    {row := 862#u16, column := 4#u8},
    {row := 863#u16, column := 4#u8},
    {row := 877#u16, column := 4#u8},
    {row := 878#u16, column := 4#u8},
    {row := 879#u16, column := 4#u8},
    {row := 893#u16, column := 4#u8},
    {row := 894#u16, column := 4#u8},
    {row := 895#u16, column := 4#u8},
    {row := 909#u16, column := 4#u8},
    {row := 910#u16, column := 4#u8},
    {row := 911#u16, column := 4#u8},
    {row := 912#u16, column := 4#u8},
    {row := 915#u16, column := 4#u8},
    {row := 916#u16, column := 4#u8},
    {row := 919#u16, column := 4#u8},
    {row := 920#u16, column := 4#u8},
    {row := 923#u16, column := 4#u8},
    {row := 924#u16, column := 4#u8},
    {row := 927#u16, column := 4#u8},
    {row := 928#u16, column := 4#u8},
    {row := 931#u16, column := 4#u8},
    {row := 932#u16, column := 4#u8},
    {row := 935#u16, column := 4#u8},
    {row := 936#u16, column := 4#u8},
    {row := 939#u16, column := 4#u8},
    {row := 940#u16, column := 4#u8},
    {row := 943#u16, column := 4#u8},
    {row := 944#u16, column := 4#u8},
    {row := 947#u16, column := 4#u8},
    {row := 948#u16, column := 4#u8},
    {row := 951#u16, column := 4#u8},
    {row := 952#u16, column := 4#u8},
    {row := 955#u16, column := 4#u8},
    {row := 956#u16, column := 4#u8},
    {row := 959#u16, column := 4#u8},
    {row := 960#u16, column := 4#u8},
    {row := 963#u16, column := 4#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_16 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_16
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_16 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 718 4; exact PV_CBM_InventoryShape.free_padding 718 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 719 4; exact PV_CBM_InventoryShape.free_padding 719 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 733 4; exact PV_CBM_InventoryShape.free_padding 733 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 734 4; exact PV_CBM_InventoryShape.free_padding 734 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 735 4; exact PV_CBM_InventoryShape.free_padding 735 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 749 4; exact PV_CBM_InventoryShape.free_padding 749 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 750 4; exact PV_CBM_InventoryShape.free_padding 750 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 751 4; exact PV_CBM_InventoryShape.free_padding 751 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 765 4; exact PV_CBM_InventoryShape.free_padding 765 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 766 4; exact PV_CBM_InventoryShape.free_padding 766 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 767 4; exact PV_CBM_InventoryShape.free_padding 767 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 781 4; exact PV_CBM_InventoryShape.free_padding 781 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 782 4; exact PV_CBM_InventoryShape.free_padding 782 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 783 4; exact PV_CBM_InventoryShape.free_padding 783 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 797 4; exact PV_CBM_InventoryShape.free_padding 797 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 798 4; exact PV_CBM_InventoryShape.free_padding 798 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 799 4; exact PV_CBM_InventoryShape.free_padding 799 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 813 4; exact PV_CBM_InventoryShape.free_padding 813 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 814 4; exact PV_CBM_InventoryShape.free_padding 814 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 815 4; exact PV_CBM_InventoryShape.free_padding 815 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 829 4; exact PV_CBM_InventoryShape.free_padding 829 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 830 4; exact PV_CBM_InventoryShape.free_padding 830 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 831 4; exact PV_CBM_InventoryShape.free_padding 831 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 845 4; exact PV_CBM_InventoryShape.free_padding 845 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 846 4; exact PV_CBM_InventoryShape.free_padding 846 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 847 4; exact PV_CBM_InventoryShape.free_padding 847 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 861 4; exact PV_CBM_InventoryShape.free_padding 861 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 862 4; exact PV_CBM_InventoryShape.free_padding 862 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 863 4; exact PV_CBM_InventoryShape.free_padding 863 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 877 4; exact PV_CBM_InventoryShape.free_padding 877 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 878 4; exact PV_CBM_InventoryShape.free_padding 878 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 879 4; exact PV_CBM_InventoryShape.free_padding 879 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 893 4; exact PV_CBM_InventoryShape.free_padding 893 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 894 4; exact PV_CBM_InventoryShape.free_padding 894 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 895 4; exact PV_CBM_InventoryShape.free_padding 895 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 909 4; exact PV_CBM_InventoryShape.free_padding 909 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 910 4; exact PV_CBM_InventoryShape.free_padding 910 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 911 4; exact PV_CBM_InventoryShape.free_padding 911 4 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 912 4; exact (PV_CBM_PathClassification.pathFree_mod 912 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 915 4; exact (PV_CBM_PathClassification.pathFree_mod 915 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 916 4; exact (PV_CBM_PathClassification.pathFree_mod 916 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 919 4; exact (PV_CBM_PathClassification.pathFree_mod 919 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 920 4; exact (PV_CBM_PathClassification.pathFree_mod 920 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 923 4; exact (PV_CBM_PathClassification.pathFree_mod 923 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 924 4; exact (PV_CBM_PathClassification.pathFree_mod 924 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 927 4; exact (PV_CBM_PathClassification.pathFree_mod 927 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 928 4; exact (PV_CBM_PathClassification.pathFree_mod 928 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 931 4; exact (PV_CBM_PathClassification.pathFree_mod 931 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 932 4; exact (PV_CBM_PathClassification.pathFree_mod 932 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 935 4; exact (PV_CBM_PathClassification.pathFree_mod 935 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 936 4; exact (PV_CBM_PathClassification.pathFree_mod 936 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 939 4; exact (PV_CBM_PathClassification.pathFree_mod 939 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 940 4; exact (PV_CBM_PathClassification.pathFree_mod 940 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 943 4; exact (PV_CBM_PathClassification.pathFree_mod 943 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 944 4; exact (PV_CBM_PathClassification.pathFree_mod 944 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 947 4; exact (PV_CBM_PathClassification.pathFree_mod 947 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 948 4; exact (PV_CBM_PathClassification.pathFree_mod 948 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 951 4; exact (PV_CBM_PathClassification.pathFree_mod 951 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 952 4; exact (PV_CBM_PathClassification.pathFree_mod 952 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 955 4; exact (PV_CBM_PathClassification.pathFree_mod 955 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 956 4; exact (PV_CBM_PathClassification.pathFree_mod 956 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 959 4; exact (PV_CBM_PathClassification.pathFree_mod 959 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 960 4; exact (PV_CBM_PathClassification.pathFree_mod 960 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 963 4; exact (PV_CBM_PathClassification.pathFree_mod 963 4 ⟨by decide,by decide⟩).mpr (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk16
