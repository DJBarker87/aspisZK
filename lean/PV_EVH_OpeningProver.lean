import PV_EVH_ExpandedProver
import PV_EVH_OpeningInstall
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpeningProver
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash AccountInst)
open PV_EVH_RetryBody (Store Outcome)
open PV_EVH_Entropy (EntropyAnswers)
open PV_EVH_ProverSpine (Head HeadFixed)
open PV_EVH_LeafInstall
variable [ExternalTypes] [ExternalFuns]

/-- Source-spine composition only. Every remaining native leaf and its
observation/allocator/formatting adequacy is OPEN; no success is asserted. -/
def entry_OPEN {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : WithCallees) (r : ReserveCallees)
    (files : PV_EVH_NonceWorld.Answers)
    (fallibleCallees : PV_EVH_NonceReserveFallible.Callees)
    (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)
    (guard_OPEN : transport.Variant → P Bool)
    (applyCallees : PV_EVH_ApplyMaterial.Callees)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltCallees : PV_EVH_PrivateSalts.Callees)
    (prepare : PV_EVH_PrepareOpening.Callees) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_PublishCompact.Callees)
    (materialCallees : PV_EVH_MaterialFromEntropy.Callees) : P Outcome :=
  PV_EVH_NonceProver.entry_OPEN inst retryFuel entropyFuel answers entropy nonzero_OPEN
    public1 compiled hash store account account_OPEN h
    (installWith b applyCallees buildCallees saltCallees (PV_EVH_OpeningInstall.install prepare finish publish))
    (installReserve r materialCallees) files fallibleCallees pathCallees nonceCallees guard_OPEN

theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : WithCallees) (r : ReserveCallees)
    (files : PV_EVH_NonceWorld.Answers)
    (fallibleCallees : PV_EVH_NonceReserveFallible.Callees)
    (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)
    (guard_OPEN : transport.Variant → P Bool)
    (applyCallees : PV_EVH_ApplyMaterial.Callees)
    (buildCallees : PV_EVH_BuildSemantics.Callees)
    (saltCallees : PV_EVH_PrivateSalts.Callees)
    (prepare : PV_EVH_PrepareOpening.Callees) (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_PublishCompact.Callees)
    (materialCallees : PV_EVH_MaterialFromEntropy.Callees)
    (he : PV_EVH_EntropyStep.Compatible entropy)
    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))
    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (hh : HeadFixed h hash) (hb : WithCompatible b) (hr : ReserveCompatible r)
    (hf : PV_EVH_NonceWorld.Compatible files)
    (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees)
    (path_same : PV_EVH_NoncePath.Compatible pathCallees)
    (nonce_same : PV_EVH_NonceReserve.Compatible nonceCallees)
    (ha : PV_EVH_ApplyMaterial.Compatible applyCallees)
    (hbuild : PV_EVH_BuildSemantics.Compatible buildCallees)
    (hsalt : PV_EVH_PrivateSalts.Compatible saltCallees)
    (hprepare : PV_EVH_PrepareOpening.Compatible prepare)
    (hfinish : PV_EVH_FinishOpening.Compatible finish)
    (hpublish : PV_EVH_PublishCompact.Compatible publish)
    (hmaterial : PV_EVH_MaterialFromEntropy.Compatible materialCallees) :
    FinishedView (entry_OPEN inst retryFuel entropyFuel answers entropy nonzero_OPEN
      public1 compiled hash store account account_OPEN h b r files fallibleCallees pathCallees
      nonceCallees guard_OPEN applyCallees buildCallees saltCallees prepare finish publish materialCallees)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  exact PV_EVH_NonceProver.entry_fixed inst retryFuel entropyFuel answers entropy nonzero_OPEN
    public1 compiled hash store account account_OPEN h
    (installWith b applyCallees buildCallees saltCallees (PV_EVH_OpeningInstall.install prepare finish publish))
    (installReserve r materialCallees) files fallibleCallees pathCallees nonceCallees guard_OPEN
    he hn guard_fixed same account_fixed hh
    (installWith_fixed b applyCallees buildCallees saltCallees (PV_EVH_OpeningInstall.install prepare finish publish) hb ha hbuild hsalt (PV_EVH_OpeningInstall.install_fixed prepare finish publish hprepare hfinish hpublish))
    (installReserve_fixed r materialCallees hr hmaterial) hf fallible_same path_same nonce_same

#print axioms entry_fixed
end PV_EVH_OpeningProver
