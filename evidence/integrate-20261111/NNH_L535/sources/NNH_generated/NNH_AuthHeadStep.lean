import NNH_SevenAccounts
set_option autoImplicit false
noncomputable section
namespace NNH_AuthHeadStep
open Aeneas Aeneas.Std AdapterRw

theorem source (ops : Ops) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (guards : NNH_AuthNativeGuards.Packet ops program pool p m c l r e v) :
 r1_pool_adapter.owned.authenticate_asq8_accounts ops program (NNH_SevenAccounts.value p m c l r e v) pool lane slot =
 NNH_AuthNativeFission.tail ops program m c l r e pool lane slot := by
 rw [NNH_AuthNativeFission.source]
 unfold NNH_AuthNativeFission.head
 rw [NNH_SevenAccounts.length]
 rcases NNH_SevenAccounts.indices p m c l r e v with ⟨i0,i1,i2,i3,i4,i5,i6⟩
 simp only [if_pos rfl,i0,i1,i2,i3,i4,i5,i6,bind_tc_ok,guards.proofGuard,guards.checkpointGuard,
  guards.masterGuard,guards.checkpointOwner,guards.laneGuard,guards.distinctGuard,
  core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end NNH_AuthHeadStep
