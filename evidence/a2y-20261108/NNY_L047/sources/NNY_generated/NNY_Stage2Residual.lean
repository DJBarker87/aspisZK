import NNU_Stage2Tail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_Stage2Residual
open Aeneas Aeneas.Std Result
/-- Error mapping never converts a verifier error into successful Stage2.
With the reached successful emit, the native tail succeeds exactly when its
actual op11 call succeeds. This is not an NND_A2 field. -/
theorem continuation_iff (ops : AdapterRw.Ops) (statement : LIBB_PoolCarriers.Statement)
 (pub proof ck : Slice U8) (emit : ops.op53 statement=ok (.Ok ())) :
 NNH_Stage2To064.continuation ops statement pub proof ck=ok (.Ok ()) ↔
 ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) pub proof ck () none=ok (.Ok ()) := by
 constructor
 · intro success
   cases called : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) pub proof ck () none with
   | fail e =>
     unfold NNH_Stage2To064.continuation at success
     rw [called] at success
     cases success
   | div =>
     unfold NNH_Stage2To064.continuation at success
     rw [called] at success
     cases success
   | ok result =>
     cases result with
     | Ok u => cases u; rfl
     | Err e =>
       unfold NNH_Stage2To064.continuation at success
       rw [called] at success
       cases mapped : ops.op44 e with
       | fail panic =>
         simp only [bind_tc_ok,core.result.Result.map_err,Port4C_GeometryStd.mapError,mapped,bind_tc_fail] at success
         cases success
       | div =>
         simp only [bind_tc_ok,core.result.Result.map_err,Port4C_GeometryStd.mapError,mapped,bind_tc_div] at success
         cases success
       | ok error =>
         simp only [bind_tc_ok,core.result.Result.map_err,Port4C_GeometryStd.mapError,mapped,
           core.result.Result.Insts.CoreOpsTry.branch] at success
         cases success
 · intro called
   exact NNU_Stage2Tail.tail ops statement pub proof ck called emit
#print axioms continuation_iff
end AspisR1.NNY_Stage2Residual
end
