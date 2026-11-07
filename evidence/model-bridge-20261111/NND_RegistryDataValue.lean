import NND_RegistryStd
import NND_AccountLaws
import NND_ProgramControl
set_option autoImplicit false
noncomputable section
namespace NND_RegistryDataValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply bytes) (r1_pool_adapter.owned.OwnedAccount.data (NND_RegistryOps.install base D env) a) =
 ok (account a).data := by
 rw [NND_RegistryStd.data]
 cases h : a.bytes <;> simp [outer,reply,bytes,account,RSL.OwnedAccount.data,h,alloc.vec.Vec.deref]

/-- Exact getter prefix with the continuation transported at the SAME slice.
The continuation lemma is a local composition premise, not a root clause. -/
theorem bind_value {B X : Type} (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (g : B → X)
 (k : Slice U8 → NND_ProgramControl.P B) (f : RSL.Bytes → Except RSL.ProgramError X)
 (hk : ∀ b, outer (reply g) (k b) = ok (f (bytes b))) :
 outer (reply g) (NND_ProgramControl.tryThen
  (r1_pool_adapter.owned.OwnedAccount.data (NND_RegistryOps.install base D env) a) k) =
 ok (NND_Returned.ebind (account a).data f) := by
 rw [NND_RegistryStd.data]
 have step := NND_ProgramControl.transport
  (match a.bytes with | .Ok b => .Ok b.deref | .Err e => .Err e) k bytes g f hk
 cases h : a.bytes <;>
  simpa [reply,account,RSL.OwnedAccount.data,bytes,h,alloc.vec.Vec.deref] using step

#print axioms value
#print axioms bind_value
end NND_RegistryDataValue
end
