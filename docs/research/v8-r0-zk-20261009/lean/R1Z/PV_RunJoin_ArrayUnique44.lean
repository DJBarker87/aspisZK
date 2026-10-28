import R1Z.PV_RunJoin_WideUnique44
import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayUnique44
open Aeneas Aeneas.Std
open ProverCommitWideOps48 PV_RunJoin_WideArithmetic44

theorem pointwise (n : Usize) (xs ys : Nat → Raw)
    (hx : ∀ k, k < n.val → canonical (xs k))
    (hy : ∀ k, k < n.val → canonical (ys k))
    (h : ∀ k, k < n.val → value (xs k) = value (ys k)) :
    PV_RunJoin_FoldCell44.array n xs = PV_RunJoin_FoldCell44.array n ys := by
  apply Subtype.ext
  apply congrArg List.ofFn
  funext k
  rw [PV_RunJoin_WideUnique44.unique (xs k.val) (ys k.val) (hx _ k.isLt) (hy _ k.isLt) (h _ k.isLt)]
#print axioms pointwise
end R1Z.PV_RunJoin_ArrayUnique44
