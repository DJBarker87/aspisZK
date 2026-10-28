import NBN_Audit
import NBU_Audit
set_option autoImplicit false
noncomputable section
namespace NBX_ResultComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Compose the existing two checked result laws on the SAME full record.
The only retained lower law is canonical DigestEncode, as in NBU's U03/U04
callee bridges. Neither a successful child nor a caller result is assumed. -/
theorem result_model (enc : NBN_EncoderSummary.Encode)
    (canonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc)
    (r : NBN_ResultValidator.Record) :
    NBN_ResultDependency.run enc r = ok (NBN_ResultValidator.status r) :=
  (NBN_ResultDependency.source enc canonical r).trans (NBN_ResultValidator.source r)

/-- Source-order continuation consumes precisely that Result. This does not
replace a native extraction proof, nor assume an independently chosen reply. -/
theorem continuation {B : Type} (enc : NBN_EncoderSummary.Encode)
    (canonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc)
    (r : NBN_ResultValidator.Record)
    (k : core.result.Result Unit NBN_StatementResult.Error → Result B) :
    (do let outcome ← NBN_ResultDependency.run enc r; k outcome) =
      (do let outcome ← pool_v1.pair_forest_terminal.validate_result r; k outcome) := by
  rw [NBN_ResultDependency.source enc canonical r]

#print axioms result_model
#print axioms continuation
end NBX_ResultComposition
end
