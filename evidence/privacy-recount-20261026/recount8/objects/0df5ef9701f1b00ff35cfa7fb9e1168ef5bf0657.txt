import R1Z.PV_RunJoin_ReserveHandleFields
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReserveClassification
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost PV_RunJoin_ReserveHandleFields
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev call := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve

theorem accepted_clean (self after : Store) (statement nonce : Array U8 32#usize)
    (run : call self statement nonce = .ok (true,after)) : after.last_error = none := by
  unfold call aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve at run
  obtain ⟨⟨status,middle⟩,called,tail⟩ := bind_eq_ok run
  cases status with
  | Ok accepted =>
    have same := Result.ok.inj tail
    have state_eq : middle = after := congrArg Prod.snd same
    rw [← state_eq]
    exact fallible_last_error self middle statement nonce (.Ok accepted) called
  | Err error =>
    obtain ⟨kind,_,tail⟩ := bind_eq_ok tail
    have impossible := congrArg Prod.fst (Result.ok.inj tail)
    cases impossible

theorem rejected_without_error (self after : Store) (statement nonce : Array U8 32#usize)
    (run : call self statement nonce = .ok (false,after)) (clean : after.last_error = none) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement nonce = .ok (.Ok false,after) := by
  unfold call aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve at run
  obtain ⟨⟨status,middle⟩,called,tail⟩ := bind_eq_ok run
  cases status with
  | Ok accepted =>
    have same := Result.ok.inj tail
    have flag_eq : accepted = false := congrArg Prod.fst same
    have state_eq : middle = after := congrArg Prod.snd same
    rw [flag_eq,state_eq] at called
    exact called
  | Err error =>
    obtain ⟨kind,_,tail⟩ := bind_eq_ok tail
    have same := congrArg (fun pair : Bool × Store => pair.2.last_error) (Result.ok.inj tail)
    dsimp only at same
    rw [clean] at same
    cases same

#print axioms accepted_clean
#print axioms rejected_without_error
end R1Z.PV_RunJoin_ReserveClassification
