import PV_EVH_NativeOperatorGuard
import PV_EVH_OpSaltsProver
import PV_EVH_OperatorInstall
import PV_EVH_OpLeafInstall
import PV_EVH_NonzeroInstall
import PV_EVH_OpOpeningInstall
import PV_EVH_OpPrivateSaltsFlow
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeOperatorProver
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash AccountInst)
open PV_EVH_RetryBody (Store Outcome)
open PV_EVH_Entropy (EntropyAnswers)
open PV_EVH_ProverSpine (Head HeadFixed)
open PV_EVH_OpLeafInstall
open R1Z.PV_RunJoin_NativeResidual62
variable (base : ExternalTypes) (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
  (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
local instance : ExternalTypes := types base
variable (ops : @ExternalFuns (types base))
local instance : ExternalFuns := opsNative base heap box ops

/-- Source-spine composition only. Every remaining native leaf and its
observation/allocator/formatting adequacy is OPEN; no success is asserted. -/
def entry_OPEN {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel nonzeroFuel saltFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_NonzeroInstall.Callees)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : WithCallees) (r : ReserveCallees)
    (files : PV_EVH_NonceWorld.Answers)
    (fallibleCallees : PV_EVH_NonceReserveFallible.Callees)
    (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)
    (applyCallees : PV_EVH_OperatorInstall.ApplyMaterial.Leaves)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltLeaves : PV_EVH_OpPrivateSaltsFlow.Callees)
    (saltStep : PV_EVH_OperatorInstall.PrivateSaltStep.Leaves)
    (prepare : PV_EVH_OperatorInstall.PrepareOpening.Leaves) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_OperatorInstall.PublishCompact.Leaves)
    (materialCallees : PV_EVH_OperatorInstall.MaterialFromEntropy.Leaves)
    (frames : PV_EVH_OperatorFrames.Frames) : P Outcome :=
  PV_EVH_OpSaltsProver.entry_OPEN inst retryFuel entropyFuel nonzeroFuel saltFuel answers entropy
      public1 compiled hash store account account_OPEN h b r files fallibleCallees pathCallees
      nonceCallees PV_EVH_VariantGuard.guard (PV_EVH_OperatorInstall.ApplyMaterial.install applyCallees frames) buildCallees saltLeaves (PV_EVH_OperatorInstall.PrivateSaltStep.install saltStep frames) (PV_EVH_OperatorInstall.PrepareOpening.install prepare frames) finish (PV_EVH_OperatorInstall.PublishCompact.install publish frames) (PV_EVH_OperatorInstall.MaterialFromEntropy.install materialCallees frames) frames

theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel nonzeroFuel saltFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_NonzeroInstall.Callees)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : WithCallees) (r : ReserveCallees)
    (files : PV_EVH_NonceWorld.Answers)
    (fallibleCallees : PV_EVH_NonceReserveFallible.Callees)
    (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)
    (applyCallees : PV_EVH_OperatorInstall.ApplyMaterial.Leaves)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltLeaves : PV_EVH_OpPrivateSaltsFlow.Callees)
    (saltStep : PV_EVH_OperatorInstall.PrivateSaltStep.Leaves)
    (prepare : PV_EVH_OperatorInstall.PrepareOpening.Leaves) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_OperatorInstall.PublishCompact.Leaves)
    (materialCallees : PV_EVH_OperatorInstall.MaterialFromEntropy.Leaves)
    (frames : PV_EVH_OperatorFrames.Frames)
    (he : PV_EVH_NonzeroInstall.Compatible entropy)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (hh : HeadFixed h hash) (hb : WithCompatible b) (hr : ReserveCompatible r)
    (hf : PV_EVH_NonceWorld.Compatible files)
    (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees)
    (path_same : PV_EVH_NoncePath.Compatible pathCallees)
    (nonce_same : PV_EVH_NonceReserve.Compatible nonceCallees)
    (ha : PV_EVH_OperatorInstall.ApplyMaterial.Compatible applyCallees)
    (hbuild : PV_EVH_BuildSemantics.Compatible buildCallees)
    (hsaltLeaves : PV_EVH_OpPrivateSaltsFlow.Compatible saltLeaves)
    (hsaltStep : PV_EVH_OperatorInstall.PrivateSaltStep.Compatible saltStep)
    (hprepare : PV_EVH_OperatorInstall.PrepareOpening.Compatible prepare)
    (hfinish : PV_EVH_FinishOpening.Compatible finish)
    (hpublish : PV_EVH_OperatorInstall.PublishCompact.Compatible publish)
    (hmaterial : PV_EVH_OperatorInstall.MaterialFromEntropy.Compatible materialCallees)
    (frame_fixed : PV_EVH_OperatorFrames.Compatible frames)
    :
    FinishedView (entry_OPEN base heap box ops inst retryFuel entropyFuel nonzeroFuel saltFuel answers entropy
      public1 compiled hash store account account_OPEN h b r files fallibleCallees pathCallees
      nonceCallees applyCallees buildCallees saltLeaves saltStep prepare finish publish materialCallees frames)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  exact PV_EVH_OpSaltsProver.entry_fixed inst retryFuel entropyFuel nonzeroFuel saltFuel answers entropy
      public1 compiled hash store account account_OPEN h b r files fallibleCallees pathCallees
      nonceCallees PV_EVH_VariantGuard.guard (PV_EVH_OperatorInstall.ApplyMaterial.install applyCallees frames) buildCallees saltLeaves (PV_EVH_OperatorInstall.PrivateSaltStep.install saltStep frames) (PV_EVH_OperatorInstall.PrepareOpening.install prepare frames) finish (PV_EVH_OperatorInstall.PublishCompact.install publish frames) (PV_EVH_OperatorInstall.MaterialFromEntropy.install materialCallees frames) frames
    he (PV_EVH_NativeOperatorGuard.guard_view base heap box ops) same account_fixed hh hb hr hf fallible_same path_same nonce_same (PV_EVH_OperatorInstall.ApplyMaterial.install_fixed applyCallees ha frames frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)) hbuild hsaltLeaves (PV_EVH_OperatorInstall.PrivateSaltStep.install_fixed saltStep hsaltStep frames frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)) (PV_EVH_OperatorInstall.PrepareOpening.install_fixed prepare hprepare frames frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)) hfinish (PV_EVH_OperatorInstall.PublishCompact.install_fixed publish hpublish frames frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)) (PV_EVH_OperatorInstall.MaterialFromEntropy.install_fixed materialCallees hmaterial frames frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)) frame_fixed (PV_EVH_NativeOperators.selection base heap box ops)

#print axioms entry_fixed
end PV_EVH_NativeOperatorProver
