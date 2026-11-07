import NMT_R2_EmittedLength
set_option autoImplicit false
noncomputable section
namespace NMT_R2_CheckpointOwner
open Aeneas Aeneas.Std NMT_345 NMT_R2_EmittedLength
attribute [local instance] Classical.propDecidable

def ownerCheck (keep : Bool) (a : Account) (program : Key) : Result Bool := do
 let owner ← AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner (toAccount a)
 core.cmp.impls.PartialEqShared.ne
  (AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (ops keep)) owner program

/-- Isolated owner comparison; equality instances are related propositionally,
not assumed definitionally equal across the two carrier installations. -/
theorem owner_check (keep : Bool) (a : Account) (program : Key) :
 ownerCheck keep a program = .ok (decide (a.owner ≠ program)) := by
 by_cases h : a.owner = program <;>
  simp [ownerCheck,AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner,
   core.cmp.impls.PartialEqShared.ne,AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
   core.cmp.PartialEq.ne.default,ops,NGL_CheckpointModel.install,toAccount,h]
#print axioms owner_check
end NMT_R2_CheckpointOwner
end
