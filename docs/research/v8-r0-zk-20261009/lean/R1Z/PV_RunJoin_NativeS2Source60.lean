import R1Z.PV_RunJoin_CaptureSource60
import R1Z.PV_RunJoin_NativeVariantTransport55
import R1Z.PV_RunJoin_NativeControlSource55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeS2Source60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ResultRelation55
variable [ExternalTypes] [ExternalFuns]

def callback (p : Phase) := prover.prove_from_semantics p.public1 .S2 p.hash p.backend p.sem p.salts

theorem reflexive {A E : Type} (r : Result (core.result.Result A E)) : Rel (CoreRel Eq) r r := by
  cases r with
  | fail e => exact .fail e
  | div => exact .div
  | ok r => cases r with
    | Ok a => exact .ok (.ok rfl)
    | Err e => exact .ok (.err e)

theorem output_eq {A T : Type}
    {left right : Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T)}
    (h : Rel (PV_RunJoin_NativeResult55.Output Eq) left right) : left=right := by
  cases h with
  | fail e => rfl
  | div => rfl
  | @ok left right h =>
    rcases left with ⟨l,ls⟩
    rcases right with ⟨r,rs⟩
    rcases h with ⟨h,hs⟩
    cases h with
    | err e => cases hs; rfl
    | @ok l r h =>
      rcases l with ⟨lv,la⟩
      rcases r with ⟨rv,ra⟩
      rcases h with ⟨hv,ha⟩
      cases hv; cases ha; cases hs; rfl

theorem execute {T : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T) :
    PV_RunJoin_NativePublication55.execute store input=
      PV_RunJoin_NativeControl55.run callback store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store := by
  unfold PV_RunJoin_NativePublication55.execute
  rw [PV_RunJoin_NativeControlSource55.complete]
  apply output_eq
  apply PV_RunJoin_NativeVariantTransport55.complete Eq _ _ store input.public1 input.compiled .S2
  intro p hv
  change Rel (CoreRel Eq)
    (prover.prove_from_semantics p.public1 p.variant p.hash p.backend p.sem p.salts)
    (prover.prove_from_semantics p.public1 .S2 p.hash p.backend p.sem p.salts)
  rw [hv]
  exact reflexive _

#print axioms reflexive
#print axioms output_eq
#print axioms execute
end R1Z.PV_RunJoin_NativeS2Source60
