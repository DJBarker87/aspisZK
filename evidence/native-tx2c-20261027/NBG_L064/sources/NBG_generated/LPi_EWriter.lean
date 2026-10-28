import ToBytesP6OutputInvariantV1
set_option autoImplicit false
namespace AspisR1.LPi_EWriter
open Aeneas Aeneas.Std Result
/-- Reuse the unchanged emitted serializer with its explicit P6 iterator model.
Native std/iterator ABI association stays in D188, not in this theorem. -/
theorem source (x : AspisR1WideToBytesSource.field.wide_exact.WideExact) :
    ∃ out, AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes x = ok out ∧
      out.val = P6ToBytes.OutputInvariant.serializedWords x :=
  P6ToBytes.OutputInvariant.to_le_bytes_output_contents x

#print axioms source
end AspisR1.LPi_EWriter
