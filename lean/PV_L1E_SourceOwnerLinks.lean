import PV_L1E_OwnerJoin
import PV_L1E_RetrySource
set_option autoImplicit false
noncomputable section
namespace PV_L1E_SourceOwnerLinks
open Aeneas Aeneas.Std Result ProverRwFull
open R1Z ProverRwRetryModel ProverCommitSemanticTransport26
open R1Z.SideChannelL1AttemptRecord (Owner eraseOwner)
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Original D163 complete control/state association. Its totality boundary
must not be assumed for an outer-failed or divergent source attempt. -/
def PV_L1E_Link_OwnerControl {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (owner : Owner (C × Store) Proof) : Prop :=
  ∀ k s, ProverRwRetryModel.attempt entropy pub compiled variant hash k s = eraseOwner owner k s

/-- Original per-attempt ordered event association, distinct from erasure. -/
def PV_L1E_Link_OwnerEvents {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (owner : Owner (C × Store) Proof) : Prop :=
  ∀ k s, (PV_L1E_RetrySource.attempt entropy pub compiled variant hash k s).events =
    (owner k s).1.events

/-- The checked source erasure supplies the value part; the two original-owner
links still need their concrete instance. No Link definition is weakened. -/
theorem source_owner {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (owner : Owner (C × Store) Proof)
    (control : PV_L1E_Link_OwnerControl entropy pub compiled variant hash owner)
    (events : PV_L1E_Link_OwnerEvents entropy pub compiled variant hash owner) :
    PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) owner := by
  intro k s
  have hr := PV_L1E_RetrySource.attempt_erasure entropy pub compiled variant hash k s
  rw [control k s] at hr
  have he := events k s
  cases step : owner k s with
  | mk record after =>
    simp only [eraseOwner,step] at hr
    simp only [step] at he
    cases leaf : PV_L1E_RetrySource.attempt entropy pub compiled variant hash k s with
    | mk es status =>
      simp only [leaf,erase] at hr
      simp only [leaf] at he
      change (⟨es,status⟩ : Logged _) = ⟨record.events,.ok (record.result,after)⟩
      rw [hr,he]
#print axioms source_owner
end PV_L1E_SourceOwnerLinks
