import PV_B3P_ByteLayout226
namespace PV_B3P_ByteEndian226
open Aeneas Aeneas.Std PV_B3P_ByteLayout226
set_option autoImplicit false

-- Four/eight fixed byte lanes, with a symbolic input word. These do not
-- normalize a serializer recurrence or any concrete field multiplication.
theorem word_bytes (v : U32) : wordBytes v = (core.num.U32.to_le_bytes v).val := by
  rfl

theorem index_bytes (v : U64) : indexBytes v = (core.num.U64.to_le_bytes v).val := by
  rfl

#print axioms word_bytes
#print axioms index_bytes
end PV_B3P_ByteEndian226
