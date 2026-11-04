import NFD_RequestDomains
import NEU_PublicProjections
import JHf_Carrier2
set_option autoImplicit false
noncomputable section
namespace NFD_RequestProjection
open Aeneas Aeneas.Std
open NEU_PublicProjections (get)
abbrev Request := NFD_RequestDomains.Request
abbrev T := AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1

def toT (p : T) : NEU_PublicProjections.Transfer :=
  AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1 (AspisR1.JHd_RequestCarrier.privateTransfer p)
def toW (p : W) : NEU_PublicProjections.Withdrawal :=
  AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1 (AspisR1.JHd_RequestCarrier.withdrawal p)
def fromT (p : NEU_PublicProjections.Transfer) : T :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
def fromW (p : NEU_PublicProjections.Withdrawal) : W :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩
theorem transfer_roundtrip (p : T) : fromT (toT p)=p := rfl
theorem withdrawal_roundtrip (p : W) : fromW (toW p)=p := rfl

def project (s : Request) (slot : Fin 14) (i : Fin 8) (j : Fin 32) : Nat :=
  if h0 : slot.val=0 then (get s.verifier_profile j).val else
  if h1 : slot.val=1 then (get s.verifier_release j).val else
  if h2 : slot.val=2 then (get s.pool_program j).val else
  match s.«public» with
  | .PrivateTransfer p =>
    if h3 : slot.val=3 then 1 else
    if h : slot.val<12 then NEU_PublicProjections.transfer (toT p) ⟨slot.val-4,by omega⟩ i j else 0
  | .Withdrawal p =>
    if h3 : slot.val=3 then 2 else
    if h : slot.val<11 then NEU_PublicProjections.withdrawal (toW p) ⟨slot.val-4,by omega⟩ i j else
    if slot.val=12 then NEU_PublicProjections.withdrawal (toW p) ⟨7,by decide⟩ i j else
    if slot.val=13 then NEU_PublicProjections.withdrawal (toW p) ⟨8,by decide⟩ i j else 0

theorem complete (a b : Request)
    (point : ∀ slot i j, project a slot i j=project b slot i j) : a=b := by
  have hp : a.verifier_profile=b.verifier_profile := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j
  have hr : a.verifier_release=b.verifier_release := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j
  have hb : a.pool_program=b.pool_program := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j
  have pub : a.«public»=b.«public» := by
    cases ha : a.«public» with
    | PrivateTransfer p =>
      cases hq : b.«public» with
      | PrivateTransfer q =>
        have raw : toT p=toT q := by
          apply NEU_PublicProjections.transfer_ext
          intro slot i j
          have h := point ⟨slot.val+4,by omega⟩ i j
          simpa [project,ha,hq,show slot.val+4≠0 by omega,show slot.val+4≠1 by omega,
            show slot.val+4≠2 by omega,show slot.val+4≠3 by omega,show slot.val+4<12 by omega] using h
        have same := congrArg fromT raw
        simpa only [transfer_roundtrip] using congrArg AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.PrivateTransfer same
      | Withdrawal q =>
        have h := point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
        simp [project,ha,hq] at h
    | Withdrawal p =>
      cases hq : b.«public» with
      | PrivateTransfer q =>
        have h := point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
        simp [project,ha,hq] at h
      | Withdrawal q =>
        have raw : toW p=toW q := by
          apply NEU_PublicProjections.withdrawal_ext
          intro slot i j
          by_cases small : slot.val<7
          · have h := point ⟨slot.val+4,by omega⟩ i j
            simpa [project,ha,hq,show slot.val+4≠0 by omega,show slot.val+4≠1 by omega,
              show slot.val+4≠2 by omega,show slot.val+4≠3 by omega,show slot.val+4<11 by omega] using h
          · by_cases seven : slot.val=7
            · have eq : slot=⟨7,by decide⟩ := Fin.ext seven
              subst slot
              simpa [project,ha,hq] using point ⟨12,by decide⟩ i j
            · have eq : slot=⟨8,by decide⟩ := Fin.ext (by change slot.val=8;omega)
              subst slot
              simpa [project,ha,hq] using point ⟨13,by decide⟩ i j
        have same := congrArg fromW raw
        simpa only [withdrawal_roundtrip] using congrArg AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.Withdrawal same
  cases a;cases b
  congr 1 <;> assumption

#print axioms transfer_roundtrip
#print axioms withdrawal_roundtrip
#print axioms complete
end NFD_RequestProjection
