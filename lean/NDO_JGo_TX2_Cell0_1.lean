import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell0_1
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window29.c01,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨157392427#u32,976552888#u32⟩,⟨1370311228#u32,1912934365#u32⟩⟩,⟨⟨6758607#u32,798442467#u32⟩,⟨59717943#u32,767445637#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨157392427#u32,976552888#u32⟩,⟨1370311228#u32,1912934365#u32⟩⟩,⟨⟨6758607#u32,798442467#u32⟩,⟨59717943#u32,767445637#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7527 224).val.drop (32*1)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7527 1 (by decide)]
  exact JGe_Window29.selected01
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7527 224) 1#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell0_1
end
