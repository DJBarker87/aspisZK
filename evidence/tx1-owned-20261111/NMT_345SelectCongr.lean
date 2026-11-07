import NMT_345Select
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Three emitted index reads, folded only through monad congruence. -/
theorem select_congr {W : Type} (s : Parent W) (f g : Selected W → Result Ret)
 (same : ∀ a,f a = g a) : select s f = select s g := by
 unfold select
 apply AspisR1.NMT_CallTree.result_congr
 intro proof
 apply AspisR1.NMT_CallTree.result_congr
 intro pub
 apply AspisR1.NMT_CallTree.result_congr
 intro checkpoint
 exact same _
#print axioms select_congr
end NMT_345
