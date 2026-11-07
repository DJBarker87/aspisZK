import NNG_FinishReady136
import NNG_Output137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishReturn137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport

theorem returned (env : RSL.Env) (d : aspis_core.digest.Digest32 Unit)
 (pub : NMP_Emitted.Public) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Unit)
 (ch : aspis_core.state_only_prefix.r0.Challenges) (obs : NMP_Emitted.Observer)
 (out : r1_semantic.Verified Unit)
 (native : NNG_FinishAdapter137.call env d pub p t ch obs=.ok (.Ok out)) :
 NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env)
  (NNG_FinishAdapter137.childInput d (toT9 pub) (toT13 p) (toT10 t) (toT3 ch) obs)=
  .ok (.Ok (NNG_Output137.verified out)) := by
 have same:=NNG_FinishAdapter137.source env d pub p t ch obs
 rw [native] at same
 unfold NNG_FinishAdapter137.oldFinish at same
 cases h : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env)
  (NNG_FinishAdapter137.childInput d (toT9 pub) (toT13 p) (toT10 t) (toT3 ch) obs) with
 | fail e=>rw [h] at same;cases same
 | div=>rw [h] at same;cases same
 | ok r=>
   rw [h] at same
   cases r with
   | Err e=>cases same
   | Ok v=>
     have value:=core.result.Result.Ok.inj (Result.ok.inj same)
     have back:=congrArg NNG_Transport.fromT11 value
     simp only [NNG_Transport.toT11_inverse] at back
     exact congrArg (fun x=>Result.ok (core.result.Result.Ok x)) back.symm
#print axioms returned
end AspisR1.NNG_FinishReturn137
