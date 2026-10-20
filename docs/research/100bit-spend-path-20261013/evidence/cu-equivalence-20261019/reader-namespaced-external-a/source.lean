import AspisR1CanonicalReader.Types
import AspisR1CanonicalInputs.Funs
import AspisR1CanonicalStd.Funs
set_option autoImplicit false
namespace AspisR1CanonicalReader
open Aeneas Aeneas.Std Result
class Runtime where
  raw : (N : Usize) → Reader → Result (Array U8 N × Reader)
abbrev Reader.raw [Runtime] := Runtime.raw
abbrev InputE := AspisR1CanonicalInputs.field.wide_exact.WideExact
def fromInput (e : InputE) : field.wide_exact.WideExact :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
   ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def toInput (e : field.wide_exact.WideExact) : InputE :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
   ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
@[simp] theorem to_fromInput (e : InputE) : toInput (fromInput e)=e := rfl

def field.wide_exact.WideExact.from_le_bytes (bytes : Slice U8) : Result (Option field.wide_exact.WideExact) := do
 let value ← AspisR1CanonicalInputs.field.wide_exact.WideExact.from_le_bytes bytes
 .ok (value.map fromInput)
abbrev core.option.Option.ok_or := @AspisR1CanonicalStd.ok_or
#print axioms to_fromInput
end AspisR1CanonicalReader
