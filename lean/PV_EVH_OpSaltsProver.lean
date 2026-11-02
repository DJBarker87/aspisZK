import PV_EVH_OpLeafInstall
import PV_EVH_NonzeroInstall
import PV_EVH_OpOpeningInstall
import PV_EVH_OpPrivateSaltsFlow
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpSaltsProver
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash AccountInst)
open PV_EVH_RetryBody (Store Outcome)
open PV_EVH_Entropy (EntropyAnswers)
open PV_EVH_ProverSpine (Head HeadFixed)
open PV_EVH_OpLeafInstall
variable [ExternalTypes] [ExternalFuns]

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
    (guard_OPEN : transport.Variant → P Bool)
    (applyCallees : PV_EVH_OpApplyMaterial.Callees)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltLeaves : PV_EVH_OpPrivateSaltsFlow.Callees)
    (saltStep : PV_EVH_OpPrivateSaltStep.Callees)
    (prepare : PV_EVH_OpPrepareOpening.Callees) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_OpPublishCompact.Callees)
    (materialCallees : PV_EVH_OpMaterialFromEntropy.Callees)
    (frames : PV_EVH_OperatorFrames.Frames) : P Outcome :=
  PV_EVH_NonceProver.entry_OPEN inst retryFuel entropyFuel answers
    (PV_EVH_NonzeroInstall.install nonzeroFuel entropy) (PV_EVH_NonzeroFlow.run nonzeroFuel)
    public1 compiled hash store account account_OPEN h
    (installWith b applyCallees buildCallees (PV_EVH_OpPrivateSaltsFlow.install saltFuel saltLeaves saltStep frames) (PV_EVH_OpOpeningInstall.install prepare finish publish))
    (installReserve r materialCallees) files fallibleCallees pathCallees nonceCallees guard_OPEN

theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel nonzeroFuel saltFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_NonzeroInstall.Callees)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : WithCallees) (r : ReserveCallees)
    (files : PV_EVH_NonceWorld.Answers)
    (fallibleCallees : PV_EVH_NonceReserveFallible.Callees)
    (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)
    (guard_OPEN : transport.Variant → P Bool)
    (applyCallees : PV_EVH_OpApplyMaterial.Callees)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltLeaves : PV_EVH_OpPrivateSaltsFlow.Callees)
    (saltStep : PV_EVH_OpPrivateSaltStep.Callees)
    (prepare : PV_EVH_OpPrepareOpening.Callees) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_OpPublishCompact.Callees)
    (materialCallees : PV_EVH_OpMaterialFromEntropy.Callees)
    (frames : PV_EVH_OperatorFrames.Frames)
    (he : PV_EVH_NonzeroInstall.Compatible entropy)
    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (hh : HeadFixed h hash) (hb : WithCompatible b) (hr : ReserveCompatible r)
    (hf : PV_EVH_NonceWorld.Compatible files)
    (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees)
    (path_same : PV_EVH_NoncePath.Compatible pathCallees)
    (nonce_same : PV_EVH_NonceReserve.Compatible nonceCallees)
    (ha : PV_EVH_OpApplyMaterial.Compatible applyCallees)
    (hbuild : PV_EVH_BuildSemantics.Compatible buildCallees)
    (hsaltLeaves : PV_EVH_OpPrivateSaltsFlow.Compatible saltLeaves)
    (hsaltStep : PV_EVH_OpPrivateSaltStep.Compatible saltStep)
    (hprepare : PV_EVH_OpPrepareOpening.Compatible prepare)
    (hfinish : PV_EVH_FinishOpening.Compatible finish)
    (hpublish : PV_EVH_OpPublishCompact.Compatible publish)
    (hmaterial : PV_EVH_OpMaterialFromEntropy.Compatible materialCallees)
    (frame_fixed : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    FinishedView (entry_OPEN inst retryFuel entropyFuel nonzeroFuel saltFuel answers entropy
      public1 compiled hash store account account_OPEN h b r files fallibleCallees pathCallees
      nonceCallees guard_OPEN applyCallees buildCallees saltLeaves saltStep prepare finish publish materialCallees frames)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  exact PV_EVH_NonceProver.entry_fixed inst retryFuel entropyFuel answers
    (PV_EVH_NonzeroInstall.install nonzeroFuel entropy) (PV_EVH_NonzeroFlow.run nonzeroFuel)
    public1 compiled hash store account account_OPEN h
    (installWith b applyCallees buildCallees (PV_EVH_OpPrivateSaltsFlow.install saltFuel saltLeaves saltStep frames) (PV_EVH_OpOpeningInstall.install prepare finish publish))
    (installReserve r materialCallees) files fallibleCallees pathCallees nonceCallees guard_OPEN
    (PV_EVH_NonzeroInstall.install_fixed nonzeroFuel entropy he)
    (PV_EVH_NonzeroFlow.run_fixed nonzeroFuel) guard_fixed same account_fixed hh
    (installWith_fixed b applyCallees buildCallees (PV_EVH_OpPrivateSaltsFlow.install saltFuel saltLeaves saltStep frames) (PV_EVH_OpOpeningInstall.install prepare finish publish) hb ha hbuild (PV_EVH_OpPrivateSaltsFlow.install_fixed saltFuel saltLeaves saltStep hsaltLeaves hsaltStep frames frame_fixed selected) (PV_EVH_OpOpeningInstall.install_fixed prepare finish publish hprepare hfinish hpublish))
    (installReserve_fixed r materialCallees hr hmaterial) hf fallible_same path_same nonce_same

#print axioms entry_fixed
end PV_EVH_OpSaltsProver
