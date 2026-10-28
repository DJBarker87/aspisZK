import FIo_NativeFuns
import LPi_EWriter
set_option autoImplicit false
namespace NBG_WriterPorts
open Aeneas Aeneas.Std Result AspisR1
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
abbrev WE := AspisR1WideToBytesSource.field.wide_exact.WideExact

def port (x : NE) : WE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem writer_result (x : NE) : ∃ out,
    AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes (port x) = ok out ∧
      out.val = P6ToBytes.OutputInvariant.serializedWords (port x) :=
  LPi_EWriter.source (port x)

theorem word_order (x : NE) :
    P6ToBytes.OutputInvariant.serializedWords (port x) =
      [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
       x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b].flatMap
        (fun word => (core.num.U32.to_le_bytes word).val) := rfl

#print axioms writer_result
#print axioms word_order
end NBG_WriterPorts
