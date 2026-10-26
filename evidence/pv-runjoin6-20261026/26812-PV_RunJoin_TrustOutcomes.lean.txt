import R1Z.PV_RunJoin_TrustItems
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TrustBoundary
open PV_RunJoin_OsWorld PV_RunJoin_NativeEffectInterface
variable {E File Reply Time Worker : Type} [DecidableEq File]

/-- The tagged field is exactly the prior eight-leaf interpretation contract;
five filesystem constructor clauses are not five independent trust items. -/
theorem outcomes_of_identity (native : Native E File Reply Time Worker)
    (laws : Laws E File Reply Time Worker) (h : Identity native laws) :
    ∀ w call, nativeCall native w call ↔ sourceCall laws w call := by
  intro w call
  cases call with
  | entropy i reply => exact h.entropy w i reply
  | file request reply next =>
    exact PV_RunJoin_NativeEffectTransport.file_iff native laws h w next request reply
  | time outcome next =>
    exact PV_RunJoin_NativeEffectTransport.time_iff native laws h w next outcome
  | worker outcome next =>
    exact PV_RunJoin_NativeEffectTransport.worker_iff native laws h w next outcome

theorem identity_of_outcomes (native : Native E File Reply Time Worker)
    (laws : Laws E File Reply Time Worker)
    (h : ∀ w call, nativeCall native w call ↔ sourceCall laws w call) :
    Identity native laws where
  entropy := fun w i reply => h w (.entropy i reply)
  open64 := by
    intro w path flags mode reply next run
    have eq := h w (.file (.open64 path flags mode) reply next)
    simpa only [nativeCall,sourceCall,FileAllowed,run,true_and,
      PV_RunJoin_NativeEffectTransport.permitted,PV_RunJoin_OsWorld.permitted] using eq
  read := by
    intro w owner count reply next run
    have eq := h w (.file (.read owner count) reply next)
    simpa only [nativeCall,sourceCall,FileAllowed,run,true_and,
      PV_RunJoin_NativeEffectTransport.permitted,PV_RunJoin_OsWorld.permitted] using eq
  write := by
    intro w owner bytes reply next run
    have eq := h w (.file (.write owner bytes) reply next)
    simpa only [nativeCall,sourceCall,FileAllowed,run,true_and,
      PV_RunJoin_NativeEffectTransport.permitted,PV_RunJoin_OsWorld.permitted] using eq
  sync := by
    intro w owner reply next run
    have eq := h w (.file (.sync owner) reply next)
    simpa only [nativeCall,sourceCall,FileAllowed,run,true_and,
      PV_RunJoin_NativeEffectTransport.permitted,PV_RunJoin_OsWorld.permitted] using eq
  close := by
    intro w owner reply next run
    have eq := h w (.file (.close owner) reply next)
    simpa only [nativeCall,sourceCall,FileAllowed,run,true_and,
      PV_RunJoin_NativeEffectTransport.permitted,PV_RunJoin_OsWorld.permitted] using eq
  time := by
    intro w outcome next run
    have eq := h w (.time outcome next)
    simpa only [nativeCall,sourceCall,TimeAllowed,run,true_and] using eq
  worker := by
    intro w outcome next run
    have eq := h w (.worker outcome next)
    simpa only [nativeCall,sourceCall,WorkerAllowed,run,true_and] using eq

#print axioms outcomes_of_identity
#print axioms identity_of_outcomes
end R1Z.PV_RunJoin_TrustBoundary
