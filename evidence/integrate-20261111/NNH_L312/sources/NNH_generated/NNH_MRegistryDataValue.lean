import NNH_MRegistryStd
import NNH_MAccountLaws
import NNH_MProgramControl
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryDataValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply bytes) (r1_pool_adapter.owned.OwnedAccount.data (NNH_MRegistryOps.install base D env) a) =
 ok (account a).bytes := by
 rw [NNH_MRegistryStd.data]
 cases h : a.bytes <;> simp [outer,reply,bytes,account,h,alloc.vec.Vec.deref]

/-- Exact getter prefix with the continuation transported at the SAME slice.
The continuation lemma is a local composition premise, not a root clause. -/
theorem bind_value {B X : Type} (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (g : B → X)
 (k : Slice U8 → NNH_MProgramControl.P B) (f : RSL.Bytes → Except RSL.ProgramError X)
 (hk : ∀ b, outer (reply g) (k b) = ok (f (bytes b))) :
 outer (reply g) (NNH_MProgramControl.tryThen
  (r1_pool_adapter.owned.OwnedAccount.data (NNH_MRegistryOps.install base D env) a) k) =
 ok (NND_Returned.ebind (account a).bytes f) := by
 rw [NNH_MRegistryStd.data]
 have step := NNH_MProgramControl.transport
  (match a.bytes with | .Ok b => .Ok b.deref | .Err e => .Err e) k bytes g f hk
 cases h : a.bytes <;>
  simpa [reply,account,bytes,h,alloc.vec.Vec.deref] using step

#print axioms value
#print axioms bind_value
end NNH_MRegistryDataValue
end
