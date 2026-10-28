import PV_L2D_Coins
set_option autoImplicit false
namespace PV_L2D_CoinTrace
open PV_L2D_Coins

def render (attempt : UInt32) (stream : UInt8) :
    Nat → UInt64 → Bool → List Event
  | 0,_,_ => []
  | n+1,c,success => .hash attempt stream c ::
    .test (success && decide (n=0)) :: render attempt stream n (c+1) success

theorem progress (hash : State → Block) (n : Nat) (s : State) :
    0<(run hash (n+1) s).consumed := by
  simp only [run,coin]
  split <;> simp
#print axioms progress

theorem some_progress (hash : State → Block) (n : Nat) (s : State)
    (h : (run hash n s).value.isSome=true) : 0<(run hash n s).consumed := by
  cases n with
  | zero => simp [run] at h
  | succ n => exact progress hash n s
#print axioms some_progress

theorem none_consumes (hash : State → Block) (n : Nat) (s : State)
    (h : (run hash n s).value=none) : (run hash n s).consumed=n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hz : hash s=(fun _=>0)
    · simp only [run,coin,dif_pos hz] at h ⊢
      rw [ih _ h]
    · simp only [run,coin,dif_neg hz] at h
      contradiction
#print axioms none_consumes

theorem complete_trace (hash : State → Block) (n : Nat) (s : State) :
    (run hash n s).events=render s.attempt s.stream (run hash n s).consumed
      s.counter (run hash n s).value.isSome := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hz : hash s=(fun _=>0)
    · let t : State:={s with counter:=s.counter+1}
      have head : ((run hash n t).value.isSome && decide ((run hash n t).consumed=0))=false := by
        cases hv : (run hash n t).value with
        | none => simp [hv]
        | some v =>
          have hp:=some_progress hash n t (by simp [hv])
          simp [hv,Nat.ne_of_gt hp]
      simp only [run,coin,dif_pos hz,render]
      rw [ih]
      simpa only [t,head]
    · simp [run,coin,hz,render]
#print axioms complete_trace

/-- The uncapped source loop is reconstructed on every finite prefix,
without installing a finite cap or erasing a continuing zero-only prefix. -/
theorem same_receipt (left right : State → Block) (n m : Nat) (s t : State)
    (ha : s.attempt=t.attempt) (hs : s.stream=t.stream) (hc : s.counter=t.counter)
    (hk : (run left n s).consumed=(run right m t).consumed)
    (hv : (run left n s).value.isSome=(run right m t).value.isSome) :
    (run left n s).events=(run right m t).events := by
  rw [complete_trace,complete_trace,ha,hs,hc,hk,hv]
#print axioms same_receipt
end PV_L2D_CoinTrace
