import NEV_CodeFieldUse
set_option autoImplicit false
noncomputable section
namespace NEV_CodeFieldPacket
open Aeneas Aeneas.Std Result
/-- The emitted extraction root is the actual trait call checked natively. -/
theorem extracted_root (word : U32) :
    NEV_CodeFieldRaw.NEV_codefield_m31 word=ok (NEV_CodeFieldBridge.value word) := by
  exact NEV_CodeFieldBridge.total word
#print axioms extracted_root
#print axioms NEV_CodeFieldUse.basis_call
end NEV_CodeFieldPacket
end
