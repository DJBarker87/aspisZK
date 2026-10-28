import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell0_0
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window29.c00,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨786224430#u32,703871394#u32⟩,⟨1662037095#u32,489388386#u32⟩⟩,⟨⟨1903496319#u32,343834816#u32⟩,⟨677054781#u32,796156838#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨786224430#u32,703871394#u32⟩,⟨1662037095#u32,489388386#u32⟩⟩,⟨⟨1903496319#u32,343834816#u32⟩,⟨677054781#u32,796156838#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7527 224).val.drop (32*0)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7527 0 (by decide)]
  exact JGe_Window29.selected00
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7527 224) 0#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell0_0
end
