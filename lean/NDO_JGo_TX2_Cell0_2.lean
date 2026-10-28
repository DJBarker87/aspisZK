import NDO_JGo_TX2_FieldRead
import NDO_JGo_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Cell0_2
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def bytes : Array U8 32#usize := ⟨JGe_Window29.c02,by rfl⟩
def value : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨21716334#u32,945564309#u32⟩,⟨58937061#u32,1029154279#u32⟩⟩,⟨⟨722500200#u32,1586718046#u32⟩,⟨418833134#u32,257474550#u32⟩⟩⟩
def native : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨21716334#u32,945564309#u32⟩,⟨58937061#u32,1029154279#u32⟩⟩,⟨⟨722500200#u32,1586718046#u32⟩,⟨418833134#u32,257474550#u32⟩⟩⟩

theorem selected : ((JFw_Frames.window 7527 224).val.drop (32*2)).take 32=bytes.val := by
  rw [JGo_TX2_Windows.cell 7527 2 (by decide)]
  exact JGe_Window29.selected02
#print axioms selected

theorem parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes)=ok (some native) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes native).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser

theorem source : FIn_Primitives.field (JFw_Frames.window 7527 224) 2#usize=ok value :=
  JGo_TX2_FieldRead.source _ _ bytes native
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    (by rw [JFw_Frames.window_length 7527 224 (by decide)];decide)
    selected parser
#print axioms source
end AspisR1.JGo_TX2_Cell0_2
end
