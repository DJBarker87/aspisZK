-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.
import R1Z.PV_CBM_CellTypes
import R1Z.PV_CBM_PushList
import R1Z.PV_CBM_ResultLaws
import R1Z.PV_CBM_PathClassification
import R1Z.PV_CBM_ValueFree
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_CellsRaw
/-- [pv_cbm_source::reference::cells_chunk_54]:
    Source: 'reference.rs', lines 3867:0-3932:1
    Visibility: public -/
def reference.cells_chunk_54
  (out : alloc.vec.Vec aspis_statement.trace_v4.TraceCell) :
  Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
  := do
  let out1 ←
    alloc.vec.Vec.push out ({ row := 912#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out2 ←
    alloc.vec.Vec.push out1 ({ row := 913#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out3 ←
    alloc.vec.Vec.push out2 ({ row := 915#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out4 ←
    alloc.vec.Vec.push out3 ({ row := 916#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out5 ←
    alloc.vec.Vec.push out4 ({ row := 917#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out6 ←
    alloc.vec.Vec.push out5 ({ row := 919#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out7 ←
    alloc.vec.Vec.push out6 ({ row := 920#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out8 ←
    alloc.vec.Vec.push out7 ({ row := 921#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out9 ←
    alloc.vec.Vec.push out8 ({ row := 923#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out10 ←
    alloc.vec.Vec.push out9 ({ row := 924#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out11 ←
    alloc.vec.Vec.push out10 ({ row := 925#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out12 ←
    alloc.vec.Vec.push out11 ({ row := 927#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out13 ←
    alloc.vec.Vec.push out12 ({ row := 928#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out14 ←
    alloc.vec.Vec.push out13 ({ row := 929#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out15 ←
    alloc.vec.Vec.push out14 ({ row := 931#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out16 ←
    alloc.vec.Vec.push out15 ({ row := 932#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out17 ←
    alloc.vec.Vec.push out16 ({ row := 933#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out18 ←
    alloc.vec.Vec.push out17 ({ row := 935#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out19 ←
    alloc.vec.Vec.push out18 ({ row := 936#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out20 ←
    alloc.vec.Vec.push out19 ({ row := 937#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out21 ←
    alloc.vec.Vec.push out20 ({ row := 939#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out22 ←
    alloc.vec.Vec.push out21 ({ row := 940#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out23 ←
    alloc.vec.Vec.push out22 ({ row := 941#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out24 ←
    alloc.vec.Vec.push out23 ({ row := 943#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out25 ←
    alloc.vec.Vec.push out24 ({ row := 944#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out26 ←
    alloc.vec.Vec.push out25 ({ row := 945#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out27 ←
    alloc.vec.Vec.push out26 ({ row := 947#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out28 ←
    alloc.vec.Vec.push out27 ({ row := 948#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out29 ←
    alloc.vec.Vec.push out28 ({ row := 949#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out30 ←
    alloc.vec.Vec.push out29 ({ row := 951#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out31 ←
    alloc.vec.Vec.push out30 ({ row := 952#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out32 ←
    alloc.vec.Vec.push out31 ({ row := 953#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out33 ←
    alloc.vec.Vec.push out32 ({ row := 955#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out34 ←
    alloc.vec.Vec.push out33 ({ row := 956#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out35 ←
    alloc.vec.Vec.push out34 ({ row := 957#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out36 ←
    alloc.vec.Vec.push out35 ({ row := 959#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out37 ←
    alloc.vec.Vec.push out36 ({ row := 960#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out38 ←
    alloc.vec.Vec.push out37 ({ row := 961#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out39 ←
    alloc.vec.Vec.push out38 ({ row := 963#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out40 ←
    alloc.vec.Vec.push out39 ({ row := 964#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out41 ←
    alloc.vec.Vec.push out40 ({ row := 965#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out42 ←
    alloc.vec.Vec.push out41 ({ row := 967#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out43 ←
    alloc.vec.Vec.push out42 ({ row := 968#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out44 ←
    alloc.vec.Vec.push out43 ({ row := 969#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out45 ←
    alloc.vec.Vec.push out44 ({ row := 971#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out46 ←
    alloc.vec.Vec.push out45 ({ row := 972#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out47 ←
    alloc.vec.Vec.push out46 ({ row := 973#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out48 ←
    alloc.vec.Vec.push out47 ({ row := 975#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out49 ←
    alloc.vec.Vec.push out48 ({ row := 976#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out50 ←
    alloc.vec.Vec.push out49 ({ row := 977#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out51 ←
    alloc.vec.Vec.push out50 ({ row := 979#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out52 ←
    alloc.vec.Vec.push out51 ({ row := 980#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out53 ←
    alloc.vec.Vec.push out52 ({ row := 981#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out54 ←
    alloc.vec.Vec.push out53 ({ row := 983#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out55 ←
    alloc.vec.Vec.push out54 ({ row := 984#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out56 ←
    alloc.vec.Vec.push out55 ({ row := 985#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out57 ←
    alloc.vec.Vec.push out56 ({ row := 987#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out58 ←
    alloc.vec.Vec.push out57 ({ row := 988#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out59 ←
    alloc.vec.Vec.push out58 ({ row := 989#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out60 ←
    alloc.vec.Vec.push out59 ({ row := 991#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out61 ←
    alloc.vec.Vec.push out60 ({ row := 992#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out62 ←
    alloc.vec.Vec.push out61 ({ row := 993#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  let out63 ←
    alloc.vec.Vec.push out62 ({ row := 995#u16, column := 14#u8 } :
      aspis_statement.trace_v4.TraceCell)
  alloc.vec.Vec.push out63 ({ row := 996#u16, column := 14#u8 } :
    aspis_statement.trace_v4.TraceCell)
end PV_CBM_CellsRaw
namespace R1Z.PV_CBM_CellChunk54
set_option autoImplicit false
def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [
    {row := 912#u16, column := 14#u8},
    {row := 913#u16, column := 14#u8},
    {row := 915#u16, column := 14#u8},
    {row := 916#u16, column := 14#u8},
    {row := 917#u16, column := 14#u8},
    {row := 919#u16, column := 14#u8},
    {row := 920#u16, column := 14#u8},
    {row := 921#u16, column := 14#u8},
    {row := 923#u16, column := 14#u8},
    {row := 924#u16, column := 14#u8},
    {row := 925#u16, column := 14#u8},
    {row := 927#u16, column := 14#u8},
    {row := 928#u16, column := 14#u8},
    {row := 929#u16, column := 14#u8},
    {row := 931#u16, column := 14#u8},
    {row := 932#u16, column := 14#u8},
    {row := 933#u16, column := 14#u8},
    {row := 935#u16, column := 14#u8},
    {row := 936#u16, column := 14#u8},
    {row := 937#u16, column := 14#u8},
    {row := 939#u16, column := 14#u8},
    {row := 940#u16, column := 14#u8},
    {row := 941#u16, column := 14#u8},
    {row := 943#u16, column := 14#u8},
    {row := 944#u16, column := 14#u8},
    {row := 945#u16, column := 14#u8},
    {row := 947#u16, column := 14#u8},
    {row := 948#u16, column := 14#u8},
    {row := 949#u16, column := 14#u8},
    {row := 951#u16, column := 14#u8},
    {row := 952#u16, column := 14#u8},
    {row := 953#u16, column := 14#u8},
    {row := 955#u16, column := 14#u8},
    {row := 956#u16, column := 14#u8},
    {row := 957#u16, column := 14#u8},
    {row := 959#u16, column := 14#u8},
    {row := 960#u16, column := 14#u8},
    {row := 961#u16, column := 14#u8},
    {row := 963#u16, column := 14#u8},
    {row := 964#u16, column := 14#u8},
    {row := 965#u16, column := 14#u8},
    {row := 967#u16, column := 14#u8},
    {row := 968#u16, column := 14#u8},
    {row := 969#u16, column := 14#u8},
    {row := 971#u16, column := 14#u8},
    {row := 972#u16, column := 14#u8},
    {row := 973#u16, column := 14#u8},
    {row := 975#u16, column := 14#u8},
    {row := 976#u16, column := 14#u8},
    {row := 977#u16, column := 14#u8},
    {row := 979#u16, column := 14#u8},
    {row := 980#u16, column := 14#u8},
    {row := 981#u16, column := 14#u8},
    {row := 983#u16, column := 14#u8},
    {row := 984#u16, column := 14#u8},
    {row := 985#u16, column := 14#u8},
    {row := 987#u16, column := 14#u8},
    {row := 988#u16, column := 14#u8},
    {row := 989#u16, column := 14#u8},
    {row := 991#u16, column := 14#u8},
    {row := 992#u16, column := 14#u8},
    {row := 993#u16, column := 14#u8},
    {row := 995#u16, column := 14#u8},
    {row := 996#u16, column := 14#u8}
  ]
theorem length : literals.length = 64 := rfl
theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :
    PV_CBM_CellsRaw.reference.cells_chunk_54 out = PV_CBM_PushList.pushList literals out := by
  unfold PV_CBM_CellsRaw.reference.cells_chunk_54
  simp only [literals,PV_CBM_PushList.pushList,PV_CBM_ResultLaws.bind_return]
theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)
    (hc : out.val.length + 64 ≤ 4096) :
    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_54 out = ok result ∧
      result.val = out.val ++ literals := by
  rw [source]
  apply PV_CBM_PushList.pushList_spec
  simpa only [length] using hc
theorem literals_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  simp only [literals,List.forall_mem_cons]
  exact ⟨(by change PV_CBM_InventoryShape.free 912 14; exact (PV_CBM_PathClassification.pathFree_mod 912 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 913 14; exact (PV_CBM_PathClassification.pathFree_mod 913 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 915 14; exact (PV_CBM_PathClassification.pathFree_mod 915 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 916 14; exact (PV_CBM_PathClassification.pathFree_mod 916 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 917 14; exact (PV_CBM_PathClassification.pathFree_mod 917 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 919 14; exact (PV_CBM_PathClassification.pathFree_mod 919 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 920 14; exact (PV_CBM_PathClassification.pathFree_mod 920 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 921 14; exact (PV_CBM_PathClassification.pathFree_mod 921 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 923 14; exact (PV_CBM_PathClassification.pathFree_mod 923 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 924 14; exact (PV_CBM_PathClassification.pathFree_mod 924 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 925 14; exact (PV_CBM_PathClassification.pathFree_mod 925 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 927 14; exact (PV_CBM_PathClassification.pathFree_mod 927 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 928 14; exact (PV_CBM_PathClassification.pathFree_mod 928 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 929 14; exact (PV_CBM_PathClassification.pathFree_mod 929 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 931 14; exact (PV_CBM_PathClassification.pathFree_mod 931 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 932 14; exact (PV_CBM_PathClassification.pathFree_mod 932 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 933 14; exact (PV_CBM_PathClassification.pathFree_mod 933 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 935 14; exact (PV_CBM_PathClassification.pathFree_mod 935 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 936 14; exact (PV_CBM_PathClassification.pathFree_mod 936 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 937 14; exact (PV_CBM_PathClassification.pathFree_mod 937 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 939 14; exact (PV_CBM_PathClassification.pathFree_mod 939 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 940 14; exact (PV_CBM_PathClassification.pathFree_mod 940 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 941 14; exact (PV_CBM_PathClassification.pathFree_mod 941 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 943 14; exact (PV_CBM_PathClassification.pathFree_mod 943 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 944 14; exact (PV_CBM_PathClassification.pathFree_mod 944 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 945 14; exact (PV_CBM_PathClassification.pathFree_mod 945 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 947 14; exact (PV_CBM_PathClassification.pathFree_mod 947 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 948 14; exact (PV_CBM_PathClassification.pathFree_mod 948 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 949 14; exact (PV_CBM_PathClassification.pathFree_mod 949 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 951 14; exact (PV_CBM_PathClassification.pathFree_mod 951 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 952 14; exact (PV_CBM_PathClassification.pathFree_mod 952 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 953 14; exact (PV_CBM_PathClassification.pathFree_mod 953 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 955 14; exact (PV_CBM_PathClassification.pathFree_mod 955 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 956 14; exact (PV_CBM_PathClassification.pathFree_mod 956 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 957 14; exact (PV_CBM_PathClassification.pathFree_mod 957 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 959 14; exact (PV_CBM_PathClassification.pathFree_mod 959 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 960 14; exact (PV_CBM_PathClassification.pathFree_mod 960 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 961 14; exact (PV_CBM_PathClassification.pathFree_mod 961 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 963 14; exact (PV_CBM_PathClassification.pathFree_mod 963 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 964 14; exact (PV_CBM_PathClassification.pathFree_mod 964 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 965 14; exact (PV_CBM_PathClassification.pathFree_mod 965 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 967 14; exact (PV_CBM_PathClassification.pathFree_mod 967 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 968 14; exact (PV_CBM_PathClassification.pathFree_mod 968 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 969 14; exact (PV_CBM_PathClassification.pathFree_mod 969 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 971 14; exact (PV_CBM_PathClassification.pathFree_mod 971 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 972 14; exact (PV_CBM_PathClassification.pathFree_mod 972 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 973 14; exact (PV_CBM_PathClassification.pathFree_mod 973 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 975 14; exact (PV_CBM_PathClassification.pathFree_mod 975 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 976 14; exact (PV_CBM_PathClassification.pathFree_mod 976 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 977 14; exact (PV_CBM_PathClassification.pathFree_mod 977 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 979 14; exact (PV_CBM_PathClassification.pathFree_mod 979 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 980 14; exact (PV_CBM_PathClassification.pathFree_mod 980 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 981 14; exact (PV_CBM_PathClassification.pathFree_mod 981 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 983 14; exact (PV_CBM_PathClassification.pathFree_mod 983 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 984 14; exact (PV_CBM_PathClassification.pathFree_mod 984 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 985 14; exact (PV_CBM_PathClassification.pathFree_mod 985 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 987 14; exact (PV_CBM_PathClassification.pathFree_mod 987 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 988 14; exact (PV_CBM_PathClassification.pathFree_mod 988 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 989 14; exact (PV_CBM_PathClassification.pathFree_mod 989 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 991 14; exact (PV_CBM_PathClassification.pathFree_mod 991 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 992 14; exact (PV_CBM_PathClassification.pathFree_mod 992 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 993 14; exact (PV_CBM_PathClassification.pathFree_mod 993 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 995 14; exact (PV_CBM_PathClassification.pathFree_mod 995 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by change PV_CBM_InventoryShape.free 996 14; exact (PV_CBM_PathClassification.pathFree_mod 996 14 ⟨by decide,by decide⟩).mpr (by decide)),
    (by intro x hx; cases hx)⟩
#print axioms length
#print axioms source
#print axioms run
#print axioms literals_free
end R1Z.PV_CBM_CellChunk54
