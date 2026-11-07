import NLW_GetterSuccess
import NLE_CallerScope
set_option autoImplicit false
noncomputable section
namespace NLW_ActualGetterScope
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- Original returned getter, without NGL_CloneDomain.install. -/
theorem stored (ops : AdapterRw.Ops) (e : Entry) (a lo hi : Nat)
 (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot a lo hi)=.ok (.Ok bytes)) : (e.snapshot a lo hi).bytes=.Ok bytes :=
 NLW_GetterSuccess.stored ops _ bytes read
/-- Source extent on the SAME original Ops and snapshot record. -/
theorem proof_extent (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot 0 58295 58295)=.ok (.Ok bytes)) : bytes.val.length=58295 :=
 NLE_SnapshotClause.proof_bytes e bytes (stored ops e 0 58295 58295 bytes read)
theorem checkpoint_extent (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot 6 1768 1768)=.ok (.Ok bytes)) : bytes.val.length=1768 :=
 NLE_CallerScope.checkpoint e bytes (stored ops e 6 1768 1768 bytes read)
#print stored
#print proof_extent
#print checkpoint_extent
#print axioms stored
#print axioms proof_extent
#print axioms checkpoint_extent
end NLW_ActualGetterScope
