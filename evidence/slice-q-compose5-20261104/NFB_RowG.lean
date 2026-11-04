import NFB_RowLog
import NFB_RowIndex
set_option autoImplicit false
namespace NFB_RowG
open Aeneas Aeneas.Std Result NFB_RowLog

def reply (x y left right product : U32) : Array U32 5#usize :=
 Array.make 5#usize [x,y,left,right,product]

def model (query x y lineX lineY product : U32) :
    Result (core.result.Result (Array U32 5#usize) NFB_RowRef.Error × NFB_RowRef.NFB_RowLog) := do
 let u ← lift (UScalar.cast .Usize query)
 if u<262144#usize then
  let parent ← u/4#usize
  let left ← lift (Usize.wrapping_mul parent 4#usize)
  let right ← lift (Usize.wrapping_add left 3#usize)
  let doubled ← NEW_GeometryActual.aspis_core.field.M31.double product
  let z ← NEW_GeometryActual.aspis_core.field.M31.sub doubled 1#u32
  ok (.Ok (Array.make 5#usize [x,y,lineX,lineY,z]),
   state 4#usize
    (event 1#u8 (UScalar.cast .U32 u) 0#u32 x y)
    (event 2#u8 (UScalar.cast .U32 left) 0#u32 lineX 0#u32)
    (event 3#u8 (UScalar.cast .U32 right) 0#u32 lineY 0#u32)
    (event 4#u8 lineX lineX product 0#u32))
 else ok (.Err .Query,initial)

/-- Exact local G: all replies are arbitrary and every Result and ordered
log entry is preserved. The only branch input is the real constructor domain;
left/right domains follow from it and are not hypotheses. -/
theorem complete (query x y lineX lineY product : U32) :
 NFB_RowRef.NFB_row query (reply x y lineX lineY product) initial=
 model query x y lineX lineY product := by
 let u := UScalar.cast .Usize query
 by_cases bound : u.val<262144
 · obtain ⟨parent,left,right,division,leftEq,rightEq,lv,rv,lb,rb,_,_⟩ :=
     NEB_GeometryIndices.aligned NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange u bound
   have leftRun := NFB_RowIndex.admitted left lb
   have rightRun := NFB_RowIndex.admitted right rb
   have first := NFB_RowIndex.admitted u bound
   have guard : u<262144#usize := by exact bound
   dsimp only [u] at first guard division
   simp only [NFB_RowRef.NFB_row,model,reply,initial,
    first,division,←leftEq,←rightEq,leftRun,rightRun,
    NFB_RowRef.aspis_core.r0.domain.FibreIndex.get,
    core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    NFB_RowRef.NFB_row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    NFB_RowRef.NFB_row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    Array.index_usize,Array.getElem?_Usize_eq,Array.make,
    NFB_RowRef.NFB_row_product,
    NFB_RowLog.step0,NFB_RowLog.step1,NFB_RowLog.step2,NFB_RowLog.step3,
    NFB_RowPrimitives.double,NFB_RowPrimitives.subtract,
    NFB_RowRef.aspis_core.field.M31.ONE,guard,if_true,lift,bind_tc_ok,uncurry]
   -- Only five literal reply positions remain; no recurrence is unfolded.
   simp
 · have guard : ¬u<262144#usize := by exact bound
   have first : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
       ok (.Err NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange) := by
    rw [NFB_RowPrimitives.index,if_neg guard]
   dsimp only [u] at first guard
   simp only [NFB_RowRef.NFB_row,model,first,
    core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    guard,if_false,lift,bind_tc_ok,uncurry]

#print axioms complete
end NFB_RowG
