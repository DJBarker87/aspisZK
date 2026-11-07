import LIBC_S1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_P1880Discharge
open RSL
/-- The concrete decoder checks the SAME buffer's length before decoding.
This closes the new revision4 caller clause without changing345's Domain. -/
theorem decoder (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) :
 TX1_345.P1880Discharge V (LIBC_S1.library V tyPublic) := by
 intro bytes statement returned
 change LIBC_S1.decode bytes = some statement at returned
 unfold LIBC_S1.decode at returned
 by_cases length : bytes.length = 1880
 · exact length
 · rw [dif_neg length] at returned
   cases returned
#print axioms decoder
end AspisR1.NNG_P1880Discharge
