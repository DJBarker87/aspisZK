import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell1_3
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window30.c04,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1991746312#u32,1680127815#u32⟩,⟨367132205#u32,642135970#u32⟩⟩,⟨⟨324534288#u32,1803698895#u32⟩,⟨2060869689#u32,1306811144#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1991746312#u32,1680127815#u32⟩,⟨367132205#u32,642135970#u32⟩⟩,⟨⟨324534288#u32,1803698895#u32⟩,⟨2060869689#u32,1306811144#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7783 224).val.drop (32*3)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7783 3 (by decide)]
  exact JGe_Window30.selected04
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7783 224) 3#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell1_3
end
