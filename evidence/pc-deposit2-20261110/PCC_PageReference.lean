import PCC_PageImage
set_option autoImplicit false
namespace PCC
open PCA
/-- POOL:286's own mutable-slice domain; the caller must derive this from its
SAME live page guard. This is not an assumption about a child result. -/
def pageDomain (args : PageArgs) (s : PCA_State) : Prop :=
  args.guard.kind = .exclusive ∧
  NLF_RefCell.live (s.loans.state.cells args.guard.cell) args.guard.token .exclusive ∧
  (s.loans.state.cells args.guard.cell).payload.bytes.length = 8256 ∧
  args.roots.length ≤ 256

def pageReference (args : PageArgs) : Reference Unit := fun s =>
  let image := pageImage args
  let payload := {(s.loans.state.cells args.guard.cell).payload with bytes := image}
  let loans := {s.loans with state := NLF_ViewLaws.write s.loans.state args.guard payload}
  ⟨{s with loans := loans},[.copy 247 args.guard image],.ok ()⟩

def RowSpec_POOL_286 (native : PageArgs → Reference Unit) : Prop :=
  Reference.RowSpec pageDomain native pageReference
end PCC
