import NNG_LegacyConfig136
import NNG_LIBDigest
set_option autoImplicit false
namespace AspisR1.NNG_LegacyDigest136

theorem supplied (env : RSL.Env) :
 NNG_Install.digest (NNG_LIBDigest.digest env)=NGQ_Effects.dictionary (LIB_Env.hashv env) := rfl
#print axioms supplied
end AspisR1.NNG_LegacyDigest136
