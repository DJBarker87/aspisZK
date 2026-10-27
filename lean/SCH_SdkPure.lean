import SCH_IdealSdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_SdkPure
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
local notation "original" => GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std
local notation "ideal" => SCH_IdealSdk.dictionary c hashv H

theorem distinct (N : Usize) : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (N := N) ideal =
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (N := N) original := rfl

theorem checkpoint : AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ideal =
    AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint original := rfl

theorem data : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ideal =
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data original := rfl

theorem prefix_bytes : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ideal =
    AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES original := by
  rw [AspisR1.AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    AspisR1.AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]

theorem digest : AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ideal =
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 original := rfl

theorem observer : AdapterRw.observer ideal = AdapterRw.observer original := rfl

#print axioms distinct
#print axioms checkpoint
#print axioms data
#print axioms prefix_bytes
#print axioms digest
#print axioms observer
end AspisR1.SCH_SdkPure
end
