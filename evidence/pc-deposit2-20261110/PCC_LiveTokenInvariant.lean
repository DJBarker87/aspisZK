import PCC_PageReference
set_option autoImplicit false
namespace PCC
open PCA
/-- Unlike validity of the cell ledger alone, this asserts that EVERY parent
owned guard is still live. It must survive children and returning CPI. -/
def ParentLive (s : PCA_State) : Prop :=
  ∀ g ∈ s.liveGuards, NLF_RefCell.live (s.loans.state.cells g.cell) g.token g.kind

def ParentExclusive (s : PCA_State) : Prop :=
  ∀ g ∈ s.liveGuards, g.kind = .exclusive

theorem page_parent_live (args : PageArgs) (s : PCA_State) (h : ParentLive s) :
    ParentLive (pageReference args s).state := by
  intro g hg
  exact (NLF_ViewLaws.write_liveness s.loans.state args.guard _ g.token g.cell g.kind).mpr (h g hg)

theorem page_parent_exclusive (args : PageArgs) (s : PCA_State)
    (h : ParentExclusive s) : ParentExclusive (pageReference args s).state := h
#print axioms page_parent_live
#print axioms page_parent_exclusive
end PCC
