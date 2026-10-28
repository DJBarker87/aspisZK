import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell1_4
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window30.c05,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1978535775#u32,441942338#u32⟩,⟨1903384839#u32,1419904273#u32⟩⟩,⟨⟨714022330#u32,338248778#u32⟩,⟨543910808#u32,510914359#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1978535775#u32,441942338#u32⟩,⟨1903384839#u32,1419904273#u32⟩⟩,⟨⟨714022330#u32,338248778#u32⟩,⟨543910808#u32,510914359#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7783 224).val.drop (32*4)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7783 4 (by decide)]
  exact JGe_Window30.selected05
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7783 224) 4#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7783 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell1_4
end
