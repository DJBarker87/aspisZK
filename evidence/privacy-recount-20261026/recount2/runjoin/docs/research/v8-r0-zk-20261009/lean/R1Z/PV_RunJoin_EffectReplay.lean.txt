import R1Z.PV_RunJoin_EffectPaths
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EffectReplay
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel (Pub Compiled Hash)
open PV_RunJoin_EffectClient
variable [ExternalTypes] [ExternalFuns]

inductive Replay {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) :
    Nat → Nat → State N → List (State N) → Execution N → Prop where
  | cap (index : Nat) (s : State N) :
      Replay account pub compiled hash 0 index s [] ⟨s,.error .AttemptsExhausted⟩
  | done {fuel index : Nat} {s : State N} {out : Execution N}
      (step : attempt account pub compiled hash index s = out)
      (stop : out.signal ≠ .rejected) :
      Replay account pub compiled hash (fuel+1) index s [s] out
  | retry {fuel index : Nat} {s after : State N} {rest : List (State N)} {out : Execution N}
      (step : attempt account pub compiled hash index s = ⟨after,.rejected⟩)
      (tail : Replay account pub compiled hash fuel (index+1) after rest out) :
      Replay account pub compiled hash (fuel+1) index s (s::rest) out

theorem sound {N : Type} {account : ProverRwEffectCallback.Account N}
    {pub : Pub} {compiled : Compiled} {hash : Hash} {fuel index : Nat}
    {s : State N} {states : List (State N)} {out : Execution N}
    (path : Replay account pub compiled hash fuel index s states out) :
    run account pub compiled hash fuel index s = out := by
  induction path with
  | cap => rfl
  | done step stop => simp only [run,step]
  | retry step tail ih => simpa only [run,step] using ih

theorem complete {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (fuel index : Nat) (s : State N) :
    ∃ states, Replay account pub compiled hash fuel index s states
      (run account pub compiled hash fuel index s) := by
  induction fuel generalizing index s with
  | zero => exact ⟨[],.cap index s⟩
  | succ fuel ih =>
    generalize he : attempt account pub compiled hash index s = out
    by_cases stop : out.signal = .rejected
    · obtain ⟨states,path⟩ := ih (index+1) out.state
      have shape : out = ⟨out.state,.rejected⟩ := by cases out; simp_all
      have step := he.trans shape
      refine ⟨s::states,?_⟩
      simpa only [run,step] using Replay.retry step path
    · refine ⟨[s],?_⟩
      have path : Replay account pub compiled hash (fuel+1) index s [s] out := .done he stop
      convert path using 1
      simp only [run,he]

theorem length_bound {N : Type} {account : ProverRwEffectCallback.Account N}
    {pub : Pub} {compiled : Compiled} {hash : Hash} {fuel index : Nat}
    {s : State N} {states : List (State N)} {out : Execution N}
    (path : Replay account pub compiled hash fuel index s states out) : states.length ≤ fuel := by
  induction path with
  | cap => simp only [List.length_nil,Nat.le_refl]
  | done => simp only [List.length_singleton]; omega
  | retry _ _ ih => simp only [List.length_cons]; omega

theorem client_cap8 {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (s : State N) :
    ∃ states, Replay account pub compiled hash 8 0 s states (client account pub compiled hash s) ∧
      states.length ≤ 8 := by
  obtain ⟨states,path⟩ := complete account pub compiled hash 8 0 s
  exact ⟨states,path,length_bound path⟩

#print axioms sound
#print axioms complete
#print axioms length_bound
#print axioms client_cap8
end R1Z.PV_RunJoin_EffectReplay
