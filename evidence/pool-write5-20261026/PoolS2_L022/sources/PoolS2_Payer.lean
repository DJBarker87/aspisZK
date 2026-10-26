import PoolS2_PrefixSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_Payer
open Aeneas Aeneas.Std Result PoolS2_PrefixSource

def PayerOK (payer : Account) : Prop :=
  payer.is_signer = true ∧ payer.is_writable = true ∧ payer.executable = false ∧
    payer.owner = systemId

def SystemOK (system : Account) : Prop :=
  system.key = systemId ∧ system.owner = nativeLoaderId ∧ system.executable = true ∧
    system.is_signer = false ∧ system.is_writable = false

theorem accepted (payer system : Account)
    (h : processor.require_payer_and_system_program payer system = ok (.Ok ())) :
    PayerOK payer ∧ SystemOK system := by
  classical
  unfold PayerOK SystemOK
  unfold processor.require_payer_and_system_program Hiq_PoolSource.keyNe Hist_Authority.keyEq at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_Payer
end
