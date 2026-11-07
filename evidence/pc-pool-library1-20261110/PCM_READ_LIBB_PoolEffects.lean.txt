import LIBB_ScannerExtent
import LIBB_ReconstructGraph
import LIBB_PoolEncode
import LIBB_PoolEmit
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolEffects
open Aeneas Aeneas.Std RSL
abbrev scanProof := LIBB_PoolScan.scanProof
abbrev reconstruct := LIBB_PoolReconstruct.reconstruct
abbrev encodeStatement := LIBB_PoolEncode.encodeStatement
abbrev emitResult := LIBB_PoolEmit.emitResult
abbrev scan_returns := LIBB_PoolScan.returns
abbrev reconstruct_returns := LIBB_PoolReconstruct.returns
abbrev encode_returns := LIBB_PoolEncode.returns
abbrev emit_returns := LIBB_PoolEmit.returns
/-- CLOSED165 deterministic graph, with no invented allocation arm. -/
theorem encode_graph (s : LIBB_PoolCarriers.Statement) (env : Env) (o : Obs (Option Bytes)) :
 encodeStatement s env o ↔
 o = LIB_Carriers.resultObs LIBB_PoolEncode.option [] (LIBB_PoolEncode.code s) :=
 LIBB_ObservationMap.lift_graph _ _ _ _
/-- CLOSED219 deterministic graph includes its exact return-data event. -/
theorem emit_graph (s : LIBB_PoolCarriers.Statement) (env : Env) (o : Obs (Except ProgramError Unit)) :
 emitResult s env o ↔ o = LIBB_PoolEmit.observation s := Iff.rfl
abbrev reconstruct_graph := LIBB_ReconstructGraph.exact_graph
abbrev scanner_extent := LIBB_ScannerExtent.extent
#print axioms encode_graph
#print axioms emit_graph
#print axioms reconstruct_graph
#print axioms scanner_extent
#print axioms scan_returns
#print axioms reconstruct_returns
#print axioms encode_returns
#print axioms emit_returns
end LIBB_PoolEffects
end
