import FIw_CopyEndpoint
import JGa_LinkBounds
set_option autoImplicit false
namespace AspisR1.FJk_CopyDescriptor
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
def endpoint (e : CompiledPoolV1PairForestEndpoint) : R0P.CopyEndpoint :=
  ⟨⟨e.row.val%1024,Nat.mod_lt _ (by decide)⟩,
   ⟨e.slot.val%2,Nat.mod_lt _ (by decide)⟩,
   ⟨e.pattern.val%14,Nat.mod_lt _ (by decide)⟩⟩
def link (l : CompiledPoolV1PairForestLink) : R0P.CopyLink :=
  ⟨l.tag.val,⟨l.weight_kind.val%5,Nat.mod_lt _ (by decide)⟩,l.weight_level.val,
    endpoint l.producer,endpoint l.consumer⟩
def variant : PoolV1PairForestCompiledVariantV1 → R0P.Variant
  | .PrivateTransfer => .privateTransfer
  | .Withdrawal => .withdrawal
/-- Generated descriptor bounds make all total-carrier reductions identities. -/
theorem endpoint_exact (e : CompiledPoolV1PairForestEndpoint)
    (hr : e.row.val<1024) (hs : e.slot.val<2) (hp : e.pattern.val<14) :
    endpoint e=FIw_CopyEndpoint.modelEndpoint e hr hs hp := by
  unfold endpoint FIw_CopyEndpoint.modelEndpoint
  simp only [Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hp]
#print axioms endpoint_exact
end AspisR1.FJk_CopyDescriptor
