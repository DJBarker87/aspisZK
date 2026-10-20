import AspisR1RhoQuery.Types
import AspisR1RhoAccumulate.Funs
namespace AspisR1RhoQuery
open Aeneas Aeneas.Std Result
/- Computational common source operations only; no proposition fields. -/
class QueryCommon where
  prefix : {H : Type} → aspis_core.Digest32 H → verifier.View → verifier.Prepared → Array aspis_core.field.WideExact 29#usize → H → Option (verifier.Phase → Result Unit) → QueryGeometry → Usize → Result (core.result.Result (Usize × aspis_core.field.WideExact) verifier.Error)
  lineNode : Usize → Result aspis_core.field.M31
  mul : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  double : aspis_core.field.M31 → Result aspis_core.field.M31
  sub : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
abbrev source_query_prefix [QueryCommon] := QueryCommon.prefix
abbrev source_line_node [QueryCommon] := QueryCommon.lineNode
abbrev M31.mul [QueryCommon] := QueryCommon.mul
abbrev M31.double [QueryCommon] := QueryCommon.double
abbrev M31.sub [QueryCommon] := QueryCommon.sub
abbrev factored_old.accumulate_with_node := AspisR1RhoAccumulate.factored_old.accumulate_with_node
abbrev factored_new.accumulate_with_node := AspisR1RhoAccumulate.factored_new.accumulate_with_node
def verifier.mark (obs : Option (verifier.Phase → Result Unit)) (p : verifier.Phase) : Result Unit := do
  match obs with
  | none => .ok ()
  | some f => f p
end AspisR1RhoQuery
