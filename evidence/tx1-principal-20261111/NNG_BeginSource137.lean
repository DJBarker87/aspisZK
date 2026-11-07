import NNG_PublicSource137
import NMP_Install150
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BeginSource137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
open NMP_ResultTransport (outer)
open AspisR1PublicPreparation

theorem value (env : RSL.Env) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Unit) :
    outer NMP_Install150.toReply (NMP_Install150.begin_ (NNG_PublicSource137.digest env) p t) =
      AspisR1PublicPreparation.r1_wire.begin (LIB_VCode.digest env) (toT13 p) (toT10 t) := by
  rw [NMP_Install150.same,NNG_PublicSource137.digest_exact]
#print axioms value
end AspisR1.NNG_BeginSource137
