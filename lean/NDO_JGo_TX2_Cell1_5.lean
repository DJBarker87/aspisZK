import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell1_5
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window30.c06,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1007528237#u32,1634416083#u32⟩,⟨581304727#u32,654910834#u32⟩⟩,⟨⟨2056004136#u32,1365093863#u32⟩,⟨1877831918#u32,75460552#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1007528237#u32,1634416083#u32⟩,⟨581304727#u32,654910834#u32⟩⟩,⟨⟨2056004136#u32,1365093863#u32⟩,⟨1877831918#u32,75460552#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7783 224).val.drop (32*5)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7783 5 (by decide)]
  exact JGe_Window30.selected06
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7783 224) 5#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell1_5
end
