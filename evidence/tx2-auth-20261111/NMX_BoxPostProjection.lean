import NKY_BoxSource
set_option autoImplicit false
noncomputable section
namespace NMX_BoxPostProjection
open Aeneas Aeneas.Std Result AspisR1
/-- Remove only the pure typed heap observation. Actual Box identity and
payload, exact ProgramError, allocator post on returns, and every stop remain. -/
def dropHeap {A S : Type} :
 Result (core.result.Result (NKY_BoxAction.Owned A) NKY_BoxAction.PE × S × NKY_BoxFrame.Heap A) →
 Result (core.result.Result (NKY_BoxAction.Owned A) NKY_BoxAction.PE × S)
 | .ok (reply,post,_) => .ok (reply,post)
 | .fail e => .fail e
 | .div => .div

theorem attach {A S : Type} (before : NKY_BoxFrame.Heap A)
 (r : Result (core.result.Result (NKY_BoxAction.Owned A) NKY_BoxAction.PE × S)) :
 dropHeap (NKY_BoxPost.attach before r) = r := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok pair => cases pair; rfl
#print axioms attach
end NMX_BoxPostProjection
end
