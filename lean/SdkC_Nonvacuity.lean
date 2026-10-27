import SdkC_BatchPair
import SdkC_Accounting
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def modelHashv (H : Bytes → State) : SdkC_Source.Parts → Result SdkC_Source.Digest :=
  fun parts => .ok (encodeState (H (flatten parts)))

theorem model_syscall (H : Bytes → State) :
    S2W_ExtractionBoundary.P1 H H ∧
      S2W_ExtractionBoundary.RuntimeSyscall (modelHashv H) H := by
  constructor
  · exact ⟨fun _ => rfl⟩
  · constructor
    intro parts digest returned
    have same := Result.ok.inj returned
    subst digest
    exact state_roundtrip _

/-- A genuine installed leaf executes and emits one source query. This is
local model non-vacuity, not a witness of a whole accepted SDK spend. -/
theorem installed_leaf (H : Bytes → State) (kind : Usize) (opening : Slice U8)
    (length : opening.val.length = 832) :
    SdkC_BatchPair.Returning (modelHashv H) H (Port4B_LeafCode.code kind opening)
      (encodeState (H (flatten (Port4B_LeafCode.input kind opening)))) := by
  have native := (Port4B_LeafCode.native_and_reads (SdkC_Source.dictionary (modelHashv H)) () H
    (fun _ => rfl) kind opening length []).1
  apply SdkC_BatchPair.returning (modelHashv H) H H (model_syscall H).1 (model_syscall H).2
  exact (SdkC_NativeNode.source_leaf (modelHashv H) kind opening []).trans native

/-- The fixture supplies the width; it does not assume successful hashing. -/
def opening : Slice U8 := ⟨List.replicate 832 0#u8,by simp only [List.length_replicate]; scalar_tac⟩

theorem fixture (H : Bytes → State) (kind : Usize) :
    SdkC_BatchPair.Returning (modelHashv H) H (Port4B_LeafCode.code kind opening)
      (encodeState (H (flatten (Port4B_LeafCode.input kind opening)))) :=
  installed_leaf H kind opening (by change (List.replicate 832 (0#u8)).length = 832; exact List.length_replicate)

#print axioms model_syscall
#print axioms installed_leaf
#print axioms fixture
end AspisR1.SdkC_Nonvacuity
end
