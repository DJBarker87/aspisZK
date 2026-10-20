import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkArrayBridgeMore
import QueryValidatorChunks12NoHit
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexProbe
abbrev QueryArray := Array Std.U32 22#usize

theorem probe (queries : QueryArray) (index : Usize)
    (hi : index.val < 22)
    (h : verifier.validate_query_index queries index = ok (core.result.Result.Ok ())) : True := by
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  simp only [verifier.validate_query_index, hidx, hshift, bind_tc_ok] at h
  trace_state
  trivial
end AspisR1.QueryValidateIndexProbe
