import LPi_WriterValues
import ToBytesP6OutputInvariantV1
set_option autoImplicit false
namespace AspisR1.LPm_BytePorts
open Aeneas Aeneas.Std Result
abbrev RawE := OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact
abbrev RawQ := OraclePortCkptAbi2Extracted.aspis_core.field.QM31
abbrev SourceQ := AspisR1WideToBytesSource.field.QM31
abbrev SourceE := AspisR1WideToBytesSource.field.wide_exact.WideExact

def qport (x : RawQ) : SourceQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def eport (x : RawE) : SourceE := ⟨qport x.c0,qport x.c1⟩

/-- The original serializer and the checkpoint sparse-selector cohort have
distinct Rust-type owners. Port all eight words explicitly, in order. -/
theorem e_layout (x : RawE) :
    P6ToBytes.OutputInvariant.serializedWords (eport x) =
      CheckpointBytesE.rawBytes x := by
  simp only [P6ToBytes.OutputInvariant.serializedWords,P6ToBytes.Steps.sourceLimbs,
    eport,qport,CheckpointBytesE.rawBytes,CheckpointP6EncodeK.bytes,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

/-- Total emitted success with the EXACT checkpoint cohort byte value,
including the owner/type port. No serializer output is a supplied premise. -/
theorem e_source (x : RawE) :
    ∃ out, AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes (eport x) = ok out ∧
      out.val = CheckpointBytesE.rawBytes x := by
  obtain ⟨out,run,layout⟩ := P6ToBytes.OutputInvariant.to_le_bytes_output_contents (eport x)
  exact ⟨out,run,layout.trans (e_layout x)⟩

#print axioms e_layout
#print axioms e_source
end AspisR1.LPm_BytePorts
