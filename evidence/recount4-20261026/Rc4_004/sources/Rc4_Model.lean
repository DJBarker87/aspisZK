import TxS_Carriers
import F3_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc4_Model
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- No address-fit law is supplied by this carrier. -/
structure Input where
  publicBytes : Bytes
  tag : AspisV8R19.DuplexFrames.Byte
  physical : F3_Model.PhysicalPublic
  proof : RawCutProverCompiler.Proof
  stored : Bytes

def typed (i : Input) : F3_Model.Input :=
  ⟨⟨(TxS_Carriers.toTyped ⟨i.publicBytes,i.tag,[]⟩).statement⟩,i.physical,i.proof,i.stored⟩

def erase (i : F3_Model.Input) : Input :=
  ⟨i.semantic.value.pubBytes,i.semantic.value.tag,i.physical,i.proof,i.stored⟩

theorem typed_erase (i : F3_Model.Input) : typed (erase i)=i := by
  have roundtrip := TxS_Carriers.prefix_erase
    (⟨i.semantic.value,[]⟩ : RawCutTranscriptRun.ErasedPrefix)
  have publicEq := congrArg (fun p : RawCutTranscriptRun.ErasedPrefix => p.statement) roundtrip
  unfold typed erase
  rw [show (TxS_Carriers.toTyped ⟨i.semantic.value.pubBytes,i.semantic.value.tag,[]⟩).statement=
    i.semantic.value from publicEq]
  rfl

#print axioms typed_erase
end AspisR1.Rc4_Model
end
