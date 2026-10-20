import AspisR1Stage2AdoptedResume.Funs
import Stage2ResumeFixedReadPrefix

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.GeneratedPrefixBridge

abbrev GenWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev GenQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31
abbrev ReadWide := AspisR1Stage2AdoptedReader.aspis_core.field.WideExact
abbrev ReadQM := AspisR1Stage2AdoptedReader.aspis_core.field.QM31

private def genQMToRead (q : GenQM) : ReadQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

private def genWideToRead (w : GenWide) : ReadWide :=
  ⟨genQMToRead w.c0, genQMToRead w.c1⟩

private def mapDecoderOption {A B : Type} (f : A → B) (r : Result (Option A)) : Result (Option B) := do
  match r with
  | .ok o => ok (o.map f)
  | .fail e => .fail e
  | .div => .div

def readerDecodersForGenerated : AspisR1Stage2AdoptedReader.ReaderDecoders where
  unwrapArray := fun r => core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  wide := fun bytes => mapDecoderOption genWideToRead
    (AspisR1Stage2AdoptedResume.aspis_core.field.WideExact.from_le_bytes bytes)
  qm := fun bytes => mapDecoderOption genQMToRead
    (AspisR1Stage2AdoptedResume.aspis_core.field.QM31.from_le_bytes bytes)

#check AspisR1Stage2AdoptedResume.verifier.resume_read_prefix
#check AspisR1Stage2AdoptedReader.ResumeFixedPrefix.readPrefix
#check readerDecodersForGenerated

end AspisR1Stage2AdoptedReader.GeneratedPrefixBridge
