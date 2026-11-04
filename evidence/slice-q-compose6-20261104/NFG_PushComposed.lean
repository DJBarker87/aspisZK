import NFF_LoggedPush
import NFG_Primitive64
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PushComposed
open Aeneas Aeneas.Std Result
/-- Full partial private-push Result, with primitive product meaning supplied
by a checked Lean law, never by a whole-child reply hypothesis. -/
theorem private_result (self : FIo_Native.fast_pairing.canonical.Dot)
 (a b : FIo_Native.fast_pairing.canonical.Q) :
 NFF_LoggedPush.privatePush NFG_Primitive64.reply self a b =
 FIo_Native.fast_pairing.canonical.Dot.push self a b :=
 NFF_LoggedPush.private_replay NFG_Primitive64.reply NFG_Primitive64.law self a b
/-- Both public rejection branches, returned receiver and wrapping count are
retained in the same typed Result. The native packet still supplies physical association. -/
theorem public_result (self : FIo_Native.fast_pairing.EbyKDot)
 (value : NEV_DotCarrier.NE) (scalar : NEV_DotCarrier.NQ) :
 NFF_LoggedPush.publicPush NFG_Primitive64.reply self value scalar =
 FIo_Native.fast_pairing.EbyKDot.push self value scalar :=
 NFF_LoggedPush.public_replay NFG_Primitive64.reply NFG_Primitive64.law self value scalar
#print axioms private_result
#print axioms public_result
end AspisR1.NFG_PushComposed
end
