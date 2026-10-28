import NBI_BatchDomains
import NBJ_Opening

set_option autoImplicit false
namespace AspisR1.NBV_CallerBounds
open Aeneas Aeneas.Std

/-- Every reached low-byte key position selects one physical opening in the
same batch. Canonicality of the Prepared source is a separate obligation. -/
theorem opening_domain (batch : Usize) (position : Nat)
    (active : position < (Port4B_TreeCuts.count batch).val) :
    (Port4B_TreeCuts.lo batch).val+position < 22 ∧
    10055+832*((Port4B_TreeCuts.lo batch).val+position)+832 ≤ 57607 := by
  have range := NBE_BatchDomains.key_domain batch position active
  have address := NBJ_Opening.address_bounds
    ((Port4B_TreeCuts.lo batch).val+position) range.2.2
  unfold NBJ_Opening.start NBJ_Opening.finish at address
  exact ⟨range.2.2,by omega⟩

/-- Dedup can only retain or add one live cell per visited key. Starting
with zero, no byte value or leaf equality premise is required for the bound. -/
def occupied : List Bool → Nat
  | [] => 0
  | duplicate::rest => occupied rest + if duplicate then 0 else 1

theorem occupied_bound (decisions : List Bool) : occupied decisions ≤ decisions.length := by
  induction decisions with
  | nil => simp [occupied]
  | cons duplicate rest ih =>
    cases duplicate <;> simp_all [occupied]

/-- Caller n=12, rather than a hidden first-transaction bound n=10. -/
theorem tx2_scratch (decisions : List Bool) (visited : decisions.length ≤ 12) :
    occupied decisions ≤ 12 ∧ occupied decisions ≤ 16 := by
  have h := occupied_bound decisions
  omega

#print axioms opening_domain
#print axioms occupied_bound
#print axioms tx2_scratch
end AspisR1.NBV_CallerBounds
