import NHY_RegistryPipeline
import NIS_ActiveSlots
import NJY_Install
import NCX_Install
import NLA_OwnedData
import NLK_PdaSites
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
open Classical
namespace NLK_RegistryInstall
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Pda := Slice (Slice U8) → Key → Result (core.result.Result Key AdapterRw.solana_pubkey.PubkeyError)
/-- Fail-closed local base. It is NOT a release dictionary. Every registry
operation reached by the reference below is explicitly installed; a final row
root must also provide its full native stage/callee association. -/
def bottom : AdapterRw.Ops := by
 constructor <;> intros <;> exact Result.fail .panic

/-- Concrete CLOSED callees and byte projections. PDA remains the quantified
op38 reply; loader is compiled readonly data, not a PDA value assumption.
This local reference is not a positive row root or a headline premise removal. -/
def ops (pda : Pda) (loader : Key) (devnet : Bool) : AdapterRw.Ops :=
 let base := NCX_Install.install (NIJ_ActiveSlots.install (NHY_RegistrySlots.install bottom))
 {base with
  op13:=ok 1#u8
  op14:=ok 2#u8
  op15:=NHY_PolicyModel.policy
  op31:=NJQ_Canonical.registry
  op32:=NJQ_Canonical.entry
  op35:=fun e => ok e
  op36:=fun a b => ok (decide (a=b))
  op37:=fun k => ok k
  op38:=pda
  op39:=fun k => ok k
  op40:=fun k => ok k.to_slice
  op41:=ok loader
  op45:=ok (NHJ_IdPacket.pool devnet)
  op46:=ok (NHJ_IdPacket.registry devnet)}

def reference (pda : Pda) (loader : Key) (devnet : Bool)
 (verifier pool : Key) (masterAccount : NLA_OwnedData.Account)
 (master : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry entry : NLA_OwnedData.Account) (slot : U64) :=
 AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  (ops pda loader devnet) verifier pool masterAccount master registry entry slot

theorem decoders (pda : Pda) (loader : Key) (devnet : Bool) :
 (ops pda loader devnet).op15=NHY_PolicyModel.policy ∧
 (ops pda loader devnet).op31=NJQ_Canonical.registry ∧
 (ops pda loader devnet).op32=NJQ_Canonical.entry ∧
 (ops pda loader devnet).op33=NCX_Install.op33 ∧
 (ops pda loader devnet).op34=NCX_Install.op34 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem actual_reply (pda : Pda) (loader : Key) (devnet : Bool) :
 (ops pda loader devnet).op38=pda ∧ (ops pda loader devnet).op41=ok loader := ⟨rfl,rfl⟩

theorem same_data (pda : Pda) (loader : Key) (devnet : Bool) (a : NLA_OwnedData.Account) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (ops pda loader devnet) a =
 ok (NLA_OwnedData.view a) := by
 exact NLA_OwnedData.source (ops pda loader devnet) a

/-- A concrete rejection arm of the emitted234 body, with no free operation
record and no child reply/success premise. The PDA is never entered here. -/
theorem wrong_pool (pda : Pda) (loader : Key) (devnet : Bool)
 (verifier pool : Key) (masterAccount : NLA_OwnedData.Account)
 (master : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry entry : NLA_OwnedData.Account) (slot : U64)
 (bad : pool≠NHJ_IdPacket.pool devnet) :
 reference pda loader devnet verifier pool masterAccount master registry entry slot=
 ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
 let o := ops pda loader devnet
 have key : o.op39 pool=ok pool := rfl
 have poolId : o.op45=ok (NHJ_IdPacket.pool devnet) := rfl
 change AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
   o verifier pool masterAccount master registry entry slot = _
 unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
 simp only [key,poolId,NGL_ArrayEquality.ne_value,bind_tc_ok]
 have d : decide (pool=NHJ_IdPacket.pool devnet)=false := by simp [bad]
 simp only [d,Bool.not_false,if_true]
#print wrong_pool
#print axioms wrong_pool

#print decoders
#print axioms decoders
#print actual_reply
#print axioms actual_reply
#print same_data
#print axioms same_data
end NLK_RegistryInstall
