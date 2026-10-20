import Aeneas
import AspisR1Stage2ResumeSuffix.Types
import AspisR1RecordParser.Funs
import AspisR1DecodeKFullV10.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1Stage2ResumeSuffix

private def mapDecoderOption {A B : Type} (f : A → B) (r : Result (Option A)) : Result (Option B) := do
  match r with
  | .ok o => ok (o.map f)
  | .fail e => .fail e
  | .div => .div

def recordQMToGenerated (q : AspisR1RecordParser.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def actualQMToGenerated (q : AspisR1DecodeKFullV10.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def actualWideToGenerated (w : AspisR1RecordParser.field.wide_exact.WideExact) : aspis_core.field.WideExact :=
  ⟨recordQMToGenerated w.c0, recordQMToGenerated w.c1⟩

def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) : Result (core.result.Result T E) :=
  match self with
  | none => ok (.Err err)
  | some v => ok (.Ok v)

def aspis_core.field.WideExact.from_le_bytes
  (s : Slice Std.U8) : Result (Option aspis_core.field.WideExact) :=
  mapDecoderOption actualWideToGenerated
    (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes s)

def aspis_core.field.QM31.from_le_bytes
  (s : Slice Std.U8) : Result (Option aspis_core.field.QM31) :=
  mapDecoderOption actualQMToGenerated
    (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes s)
end AspisR1Stage2ResumeSuffix
