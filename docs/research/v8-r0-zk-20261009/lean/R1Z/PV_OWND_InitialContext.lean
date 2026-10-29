import R1Z.PV_OWND_LoanFresh
import R1Z.PV_OWND_InitialSuccess
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialContext
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- Ordinary incoming world invariants and retained allocator adequacy. No
initialized schedule, returned Vec, or counter-check result is assumed. -/
structure Context {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X) (owner : Nat) : Prop where
 slot_empty : w.memory.slots owner=none
 loans_live : PV_OWND_LoanFresh.LoansLive w.memory
 live_nonzero : ∀ q c, w.memory.heap q=some c → c.live=true → c.size>0
 runtime : AllocatorAdequate prim ⟨1016,2⟩ w

theorem fresh {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X) (owner p : Nat) (s : S)
 (ctx:Context prim w owner) (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s)) :
 ∀ c, w.memory.heap p=some c → c.live=true → False := by
 intro c hc hl
 have disjoint:=(ctx.runtime p s h).2.2.2 p c hc hl
 have positive:=ctx.live_nonzero p c hc hl
 omega

theorem noLoans {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X) (owner p : Nat) (s : S)
 (ctx:Context prim w owner) (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s)) :
 NoLoans w.memory ⟨p,w.memory.generations p+1⟩ :=
 PV_OWND_LoanFresh.fresh_noLoans w.memory p _ ctx.loans_live (fresh prim w owner p s ctx h)
#print axioms fresh
#print axioms noLoans
end R1Z.PV_OWND_InitialContext
