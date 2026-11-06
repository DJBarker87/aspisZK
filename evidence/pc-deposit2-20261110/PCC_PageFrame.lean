import PCC_PageReference
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA

theorem page_guard_frame (args : PageArgs) (s : PCA_State) :
    (pageReference args s).state.liveGuards = s.liveGuards ∧
    (pageReference args s).state.loans.next = s.loans.next ∧
    (pageReference args s).state.loans.events = s.loans.events := ⟨rfl,rfl,rfl⟩

theorem page_preserves (args : PageArgs) : Preserves (pageReference args) := by
  intro s hs
  exact NLF_StateLaws.write_invariant s.loans args.guard
    {(s.loans.state.cells args.guard.cell).payload with bytes := pageImage args} hs

/-- Payload writes preserve EVERY cell's borrow counter, including live guards. -/
theorem page_counter_frame (args : PageArgs) (s : PCA_State) (i : Nat) :
    NLF_RefCell.flag ((pageReference args s).state.loans.state.cells i) =
      NLF_RefCell.flag (s.loans.state.cells i) :=
  NLF_ViewLaws.write_counter s.loans.state args.guard _ i
#print axioms page_guard_frame
#print axioms page_preserves
#print axioms page_counter_frame
end PCC
