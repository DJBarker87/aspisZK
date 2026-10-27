-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_6]:
    Source: 'reference.rs', lines 699:0-764:1
    Visibility: public -/
def reference.cells_chunk_6
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 877#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 878#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 879#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 893#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 894#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 895#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 909#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 910#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 911#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 912#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 915#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 916#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 919#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 920#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 923#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 924#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 927#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 928#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 931#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 932#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 935#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 936#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 939#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 940#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 943#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 944#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 947#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 948#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 951#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 952#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 955#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 956#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 959#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 960#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 963#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 964#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 967#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 968#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 971#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 972#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 975#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 976#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 979#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 980#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 983#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 984#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 987#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 988#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 991#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 992#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 995#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 996#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 999#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 1000#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 1003#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 1004#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 1007#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 1019#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 1021#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 1023#u16, column := 1#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 13#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 14#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 15#u16, column := 2#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 29#u16, column := 2#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk06
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 877#u16, column := 1#u8},
    {row := 878#u16, column := 1#u8},
    {row := 879#u16, column := 1#u8},
    {row := 893#u16, column := 1#u8},
    {row := 894#u16, column := 1#u8},
    {row := 895#u16, column := 1#u8},
    {row := 909#u16, column := 1#u8},
    {row := 910#u16, column := 1#u8},
    {row := 911#u16, column := 1#u8},
    {row := 912#u16, column := 1#u8},
    {row := 915#u16, column := 1#u8},
    {row := 916#u16, column := 1#u8},
    {row := 919#u16, column := 1#u8},
    {row := 920#u16, column := 1#u8},
    {row := 923#u16, column := 1#u8},
    {row := 924#u16, column := 1#u8},
    {row := 927#u16, column := 1#u8},
    {row := 928#u16, column := 1#u8},
    {row := 931#u16, column := 1#u8},
    {row := 932#u16, column := 1#u8},
    {row := 935#u16, column := 1#u8},
    {row := 936#u16, column := 1#u8},
    {row := 939#u16, column := 1#u8},
    {row := 940#u16, column := 1#u8},
    {row := 943#u16, column := 1#u8},
    {row := 944#u16, column := 1#u8},
    {row := 947#u16, column := 1#u8},
    {row := 948#u16, column := 1#u8},
    {row := 951#u16, column := 1#u8},
    {row := 952#u16, column := 1#u8},
    {row := 955#u16, column := 1#u8},
    {row := 956#u16, column := 1#u8},
    {row := 959#u16, column := 1#u8},
    {row := 960#u16, column := 1#u8},
    {row := 963#u16, column := 1#u8},
    {row := 964#u16, column := 1#u8},
    {row := 967#u16, column := 1#u8},
    {row := 968#u16, column := 1#u8},
    {row := 971#u16, column := 1#u8},
    {row := 972#u16, column := 1#u8},
    {row := 975#u16, column := 1#u8},
    {row := 976#u16, column := 1#u8},
    {row := 979#u16, column := 1#u8},
    {row := 980#u16, column := 1#u8},
    {row := 983#u16, column := 1#u8},
    {row := 984#u16, column := 1#u8},
    {row := 987#u16, column := 1#u8},
    {row := 988#u16, column := 1#u8},
    {row := 991#u16, column := 1#u8},
    {row := 992#u16, column := 1#u8},
    {row := 995#u16, column := 1#u8},
    {row := 996#u16, column := 1#u8},
    {row := 999#u16, column := 1#u8},
    {row := 1000#u16, column := 1#u8},
    {row := 1003#u16, column := 1#u8},
    {row := 1004#u16, column := 1#u8},
    {row := 1007#u16, column := 1#u8},
    {row := 1019#u16, column := 1#u8},
    {row := 1021#u16, column := 1#u8},
    {row := 1023#u16, column := 1#u8},
    {row := 13#u16, column := 2#u8},
    {row := 14#u16, column := 2#u8},
    {row := 15#u16, column := 2#u8},
    {row := 29#u16, column := 2#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_6 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_6
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_6 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 877 1; exact PV_CBM_InventoryShape.free_padding 877 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 878 1; exact PV_CBM_InventoryShape.free_padding 878 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 879 1; exact PV_CBM_InventoryShape.free_padding 879 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 893 1; exact PV_CBM_InventoryShape.free_padding 893 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 894 1; exact PV_CBM_InventoryShape.free_padding 894 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 895 1; exact PV_CBM_InventoryShape.free_padding 895 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 909 1; exact PV_CBM_InventoryShape.free_padding 909 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 910 1; exact PV_CBM_InventoryShape.free_padding 910 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 911 1; exact PV_CBM_InventoryShape.free_padding 911 1 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 912 1; exact (PV_CBM_PathClassification.pathFree_mod 912 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 915 1; exact (PV_CBM_PathClassification.pathFree_mod 915 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 916 1; exact (PV_CBM_PathClassification.pathFree_mod 916 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 919 1; exact (PV_CBM_PathClassification.pathFree_mod 919 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 920 1; exact (PV_CBM_PathClassification.pathFree_mod 920 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 923 1; exact (PV_CBM_PathClassification.pathFree_mod 923 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 924 1; exact (PV_CBM_PathClassification.pathFree_mod 924 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 927 1; exact (PV_CBM_PathClassification.pathFree_mod 927 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 928 1; exact (PV_CBM_PathClassification.pathFree_mod 928 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 931 1; exact (PV_CBM_PathClassification.pathFree_mod 931 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 932 1; exact (PV_CBM_PathClassification.pathFree_mod 932 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 935 1; exact (PV_CBM_PathClassification.pathFree_mod 935 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 936 1; exact (PV_CBM_PathClassification.pathFree_mod 936 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 939 1; exact (PV_CBM_PathClassification.pathFree_mod 939 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 940 1; exact (PV_CBM_PathClassification.pathFree_mod 940 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 943 1; exact (PV_CBM_PathClassification.pathFree_mod 943 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 944 1; exact (PV_CBM_PathClassification.pathFree_mod 944 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 947 1; exact (PV_CBM_PathClassification.pathFree_mod 947 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 948 1; exact (PV_CBM_PathClassification.pathFree_mod 948 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 951 1; exact (PV_CBM_PathClassification.pathFree_mod 951 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 952 1; exact (PV_CBM_PathClassification.pathFree_mod 952 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 955 1; exact (PV_CBM_PathClassification.pathFree_mod 955 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 956 1; exact (PV_CBM_PathClassification.pathFree_mod 956 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 959 1; exact (PV_CBM_PathClassification.pathFree_mod 959 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 960 1; exact (PV_CBM_PathClassification.pathFree_mod 960 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 963 1; exact (PV_CBM_PathClassification.pathFree_mod 963 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 964 1; exact (PV_CBM_PathClassification.pathFree_mod 964 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 967 1; exact (PV_CBM_PathClassification.pathFree_mod 967 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 968 1; exact (PV_CBM_PathClassification.pathFree_mod 968 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 971 1; exact (PV_CBM_PathClassification.pathFree_mod 971 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 972 1; exact (PV_CBM_PathClassification.pathFree_mod 972 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 975 1; exact (PV_CBM_PathClassification.pathFree_mod 975 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 976 1; exact (PV_CBM_PathClassification.pathFree_mod 976 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 979 1; exact (PV_CBM_PathClassification.pathFree_mod 979 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 980 1; exact (PV_CBM_PathClassification.pathFree_mod 980 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 983 1; exact (PV_CBM_PathClassification.pathFree_mod 983 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 984 1; exact (PV_CBM_PathClassification.pathFree_mod 984 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 987 1; exact (PV_CBM_PathClassification.pathFree_mod 987 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 988 1; exact (PV_CBM_PathClassification.pathFree_mod 988 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 991 1; exact (PV_CBM_PathClassification.pathFree_mod 991 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 992 1; exact (PV_CBM_PathClassification.pathFree_mod 992 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 995 1; exact (PV_CBM_PathClassification.pathFree_mod 995 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 996 1; exact (PV_CBM_PathClassification.pathFree_mod 996 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 999 1; exact (PV_CBM_PathClassification.pathFree_mod 999 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1000 1; exact (PV_CBM_PathClassification.pathFree_mod 1000 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1003 1; exact (PV_CBM_PathClassification.pathFree_mod 1003 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1004 1; exact (PV_CBM_PathClassification.pathFree_mod 1004 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1007 1; exact (PV_CBM_PathClassification.pathFree_mod 1007 1 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1019 1; exact (PV_CBM_ValueFree.valueFree_iff 11 1 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1021 1; exact (PV_CBM_ValueFree.valueFree_iff 13 1 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 1023 1; exact (PV_CBM_ValueFree.valueFree_iff 15 1 (by decide)).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 13 2; exact PV_CBM_InventoryShape.free_padding 13 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 14 2; exact PV_CBM_InventoryShape.free_padding 14 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 15 2; exact PV_CBM_InventoryShape.free_padding 15 2 (by decide) (by decide)),
    (by change PV_CBM_InventoryShape.free 29 2; exact PV_CBM_InventoryShape.free_padding 29 2 (by decide) (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk06
