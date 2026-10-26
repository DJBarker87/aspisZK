import T2Nat_FinishResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_FinishSource
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem accepted {F : Type} (ops : FinishOps F) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (success : Port4D_FinishInstall.finish ops v p a none=ok (.Ok ())) :
    Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none=ok (.Ok ()) := by
  unfold Port4D_FinishInstall.finish at success
  change Port3_QueryInstall.result
    (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none)=ok (.Ok ()) at success
  cases called : Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none with
  | fail e=>simp only [called,Port3_QueryInstall.result,bind_tc_fail] at success;cases success
  | div=>simp only [called,Port3_QueryInstall.result,bind_tc_div] at success;cases success
  | ok r=>
    cases r with
    | Err e=>simp only [called,Port3_QueryInstall.result,bind_tc_ok] at success;cases success
    | Ok u=>cases u;rfl

#print axioms accepted
end AspisR1.F3R_FinishSource
end
