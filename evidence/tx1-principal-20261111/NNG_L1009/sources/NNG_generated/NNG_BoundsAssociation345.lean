import NNG_Tree345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BoundsAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

/-- Only the frozen scalar constants are reduced: no proof buffer or child
computation is evaluated. -/
theorem source {W : Type} (s : ProofData W) (env : RSL.Env) (events : Event → List RSL.Event) :
 observation NNG_ChildSource345.port events (NNG_TreeTail345.bounds (NNG_Calls345.calls env) s)=
 observation NNG_ChildSource345.port events (NNG_TreeTail345.tail (NNG_Calls345.calls env) ⟨s,688#usize,58295#usize⟩) := by
 rfl
#print axioms source
end AspisR1.NNG_BoundsAssociation345
