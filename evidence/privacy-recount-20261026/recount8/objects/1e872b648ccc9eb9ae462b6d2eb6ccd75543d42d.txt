import R1Z.PV_RunJoin_UnifiedRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceAccount
open Aeneas Aeneas.Std Result
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N L C : Type}
abbrev State (N L C : Type) := PV_RunJoin_UnifiedRetry.State N L C

/-- Lift the actual FnMut public-account callback by updating only its policy
state. Native callback/oracle-effect association remains a separate input. -/
def account (policy : ProverRwEffectCallback.Account N) :
    ProverRwEffectCallback.Account (State N L C) where
  FnOnceInst := { call_once := fun s k => do
    let (nonce,_) ← policy.call_mut s.policy k
    .ok nonce }
  call_mut := fun s k => do
    let (nonce,next) ← policy.call_mut s.policy k
    .ok (nonce,{s with policy := next})

theorem provider_frame (policy : ProverRwEffectCallback.Account N)
    (s next : State N L C) (k : Usize) (nonce : Array U8 32#usize)
    (run : (account policy).call_mut s k = .ok (nonce,next)) :
    next.provider = s.provider := by
  dsimp only [account] at run
  cases computation : policy.call_mut s.policy k with
  | fail e => simp only [computation,bind_tc_fail] at run; cases run
  | div => simp only [computation,bind_tc_div] at run; cases run
  | ok out =>
    rcases out with ⟨outNonce,outNext⟩
    simp only [computation,bind_tc_ok,Aeneas.Std.uncurry] at run
    have same := Result.ok.inj run
    exact congrArg (fun pair => pair.2.provider) same.symm

theorem ledger_frame (policy : ProverRwEffectCallback.Account N)
    (s next : State N L C) (k : Usize) (nonce : Array U8 32#usize)
    (run : (account policy).call_mut s k = .ok (nonce,next)) :
    next.ledger = s.ledger := by
  dsimp only [account] at run
  cases computation : policy.call_mut s.policy k with
  | fail e => simp only [computation,bind_tc_fail] at run; cases run
  | div => simp only [computation,bind_tc_div] at run; cases run
  | ok out =>
    rcases out with ⟨outNonce,outNext⟩
    simp only [computation,bind_tc_ok,Aeneas.Std.uncurry] at run
    have same := Result.ok.inj run
    exact congrArg (fun pair => pair.2.ledger) same.symm

#print axioms provider_frame
#print axioms ledger_frame
end R1Z.PV_RunJoin_SourceAccount
