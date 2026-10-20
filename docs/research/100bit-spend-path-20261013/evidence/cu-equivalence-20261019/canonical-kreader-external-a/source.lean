import AspisR1CanonicalKReader.Types
import AspisR1RhoParser.Funs
import AspisR1CanonicalStd.Funs
set_option autoImplicit false
namespace AspisR1CanonicalKReader
open Aeneas Aeneas.Std Result
class Runtime where
  raw : (N : Usize) → Reader → Result (Array U8 N × Reader)
abbrev Reader.raw [Runtime] := Runtime.raw
abbrev RhoK := AspisR1CuRho.field.QM31
def fromRho (q : RhoK) : field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toRho (q : field.QM31) : RhoK := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
@[simp] theorem to_fromRho (q : RhoK) : toRho (fromRho q)=q := rfl

def field.QM31.from_le_bytes (bytes : Slice U8) : Result (Option field.QM31) := do
 let value ← AspisR1CuRho.field.QM31.from_le_bytes bytes
 .ok (value.map fromRho)
abbrev core.option.Option.ok_or := @AspisR1CanonicalStd.ok_or
#print axioms to_fromRho
end AspisR1CanonicalKReader
