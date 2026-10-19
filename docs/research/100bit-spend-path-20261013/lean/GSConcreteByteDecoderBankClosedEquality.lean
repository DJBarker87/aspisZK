import GSConcreteByteDecoderBank
import WideExactOutputComputableEquality

set_option autoImplicit false

namespace AspisR1.GSConcreteByteDecoderBank

open M31RetryOutputFiber
open AspisR1.GSFixedInputDecoderFamily
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

local instance : DecidableEq K := wideExactOutputDecidableEq

/-- Concrete runtime entrypoint with equality dictionaries fixed by the
retained eight-limb codec. -/
def runWithRetainedEquality (inputs : Inputs K 5) (xs : RawCoins) :
    Option (Results K 5) := run inputs xs

/-- The byte sampler and decoder-bank bound closes the equality dictionaries
using the computable retained-coordinate test. -/
theorem failure_small_with_retained_equality (inputs : Inputs K 5) :
    mean (fun xs : RawCoins => indicator (failed inputs xs)) < (1/2 : ℚ)^126 := by
  exact failure_small inputs

#print axioms runWithRetainedEquality
#print axioms failure_small_with_retained_equality

end AspisR1.GSConcreteByteDecoderBank
