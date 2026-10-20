import AspisR1RhoStage.Types
import AspisR1RhoQuery.Funs
import CuSavingsRhoHeap
namespace AspisR1RhoStage
open Aeneas Aeneas.Std Result
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
-- Exact source prefix rejection precedes every mutation of a or pending.
-- Owned query outcomes expose precisely those private-local handbacks.
def stage_query_old {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry) :
    Result (core.result.Result Unit verifier.Error × verifier.Accumulator) := do
  let r ← AspisR1RhoQuery.query_old.query_with_geometry digest v p a g hash obs geometry
  match r with
  | .Err e => .ok (.Err e,a)
  | .Ok out => .ok (.Ok (),out)
def stage_query_new {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry) (b : BatchedWeights) :
    Result (core.result.Result Unit verifier.Error × verifier.Accumulator × BatchedWeights) := do
  let r ← AspisR1RhoQuery.query_new.query_with_geometry digest v p a g hash obs geometry b
  match r with
  | .Err e => .ok (.Err e,a,b)
  | .Ok (out,pending) => .ok (.Ok (),out,pending)
def BatchedWeights.new [AspisR1CuRho.HeapReserve] (weights : Slice aspis_core.field.QM31) :=
  @AspisR1CuRho.verifier.BatchedWeights.new AspisR1.CuSavingsRhoHeap.sourceAllocator weights
abbrev BatchedWeights.finish := AspisR1CuRhoSource.verifier.BatchedWeights.finish
end AspisR1RhoStage
