import R1Z.PV_OWND_AllocationBuffer
set_option autoImplicit false
namespace R1Z.PV_OWND_LoanFresh
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- A source-world invariant: every outstanding loan names a live allocation. -/
def LoansLive (m : Memory) : Prop := ∀ l ∈ m.loans, ∃ c, Live m l.token c

theorem fresh_noLoans (m : Memory) (p generation : Nat)
 (live:LoansLive m)
 (fresh:∀ c, m.heap p=some c → c.live=true → False) :
 NoLoans m ⟨p,generation⟩ := by
 intro l hl eq
 obtain ⟨c,hc⟩:=live l hl
 have address:=congrArg Token.address eq
 exact fresh c (by simpa only [address] using hc.1) hc.2.1
#print axioms fresh_noLoans
end R1Z.PV_OWND_LoanFresh
