import NNG_LengthNative345
set_option autoImplicit false
namespace AspisR1.NNG_GettersGraph345
open Aeneas Aeneas.Std NMT_345 RSL
/-- Canonical complete full-error getter laws; these are source/std supplements. -/
theorem data (keep : Bool) (a : Account) (env : Env) :
 OwnedAccount.data (account a) env (NNG_Observe345.run keep a) :=
 NNG_Observe345.data_law keep a env
#print axioms data
theorem length (keep : Bool) (a : Account) (env : Env) :
 OwnedAccount.data_len (account a) env (NNG_LengthNative345.run keep a) :=
 NNG_LengthNative345.emitted_length keep a env
#print axioms length
end AspisR1.NNG_GettersGraph345
