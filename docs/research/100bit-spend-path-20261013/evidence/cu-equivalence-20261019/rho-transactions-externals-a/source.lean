import AspisR1RhoTransactions.Types
import AspisR1RhoStage.Funs
import AspisR1RhoResumeCaller.Funs
namespace AspisR1RhoTransactions
open Aeneas Aeneas.Std Result
/- Unchanged source operations, including all suffix effects, are arbitrary
identical computations; no equivalence or success law is a field. -/
class TxCommon where
  parse : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
  parseShape : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  geometry : Array U32 22#usize → Usize → Usize → Result (core.result.Result QueryGeometry verifier.Error)
  checkpoint : {H : Type} → aspis_core.Digest32 H → verifier.Prepared → verifier.Accumulator → Slice U8 → Slice U8 → H → Result (alloc.vec.Vec U8)
  finishRelation : verifier.View → verifier.Prepared → verifier.Accumulator → Option (verifier.Phase → Result Unit) → Result (core.result.Result Unit verifier.Error)
abbrev weights.powers [TxCommon] := TxCommon.powers
abbrev verifier.View.parse [TxCommon] := TxCommon.parse
abbrev View.parse_shape [TxCommon] := TxCommon.parseShape
abbrev QueryGeometry.for_range [TxCommon] := TxCommon.geometry
abbrev checkpoint {H : Type} [TxCommon] := TxCommon.checkpoint (H:=H)
abbrev finish_relation [TxCommon] := TxCommon.finishRelation
abbrev verifier.mark := AspisR1RhoQuery.verifier.mark
abbrev verifier.Phase.Parsed := AspisR1RhoQuery.verifier.Phase.Parsed
abbrev verifier.Phase.CheckpointRead := AspisR1RhoQuery.verifier.Phase.CheckpointRead
abbrev verifier.Phase.CheckpointWrite := AspisR1RhoQuery.verifier.Phase.CheckpointWrite
abbrev source_resume {H : Type} [AspisR1RhoResumeCaller.ResumeCommon] := AspisR1RhoResumeCaller.source_resume_caller (H:=H)
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon] [AspisR1CuRho.HeapReserve]
abbrev stage_old := AspisR1RhoStage.stage_old
abbrev stage_new := AspisR1RhoStage.stage_new
end AspisR1RhoTransactions
