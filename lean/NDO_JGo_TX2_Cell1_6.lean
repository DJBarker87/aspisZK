import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell1_6
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window30.c07,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨457217806#u32,214550332#u32⟩,⟨1280429014#u32,1058658606#u32⟩⟩,⟨⟨1325225782#u32,697722630#u32⟩,⟨1125651937#u32,94446012#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨457217806#u32,214550332#u32⟩,⟨1280429014#u32,1058658606#u32⟩⟩,⟨⟨1325225782#u32,697722630#u32⟩,⟨1125651937#u32,94446012#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7783 224).val.drop (32*6)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7783 6 (by decide)]
  exact JGe_Window30.selected07
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7783 224) 6#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell1_6
end
