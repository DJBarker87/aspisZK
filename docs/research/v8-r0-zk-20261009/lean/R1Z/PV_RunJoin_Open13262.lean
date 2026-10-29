import R1Z.PV_RunJoin_ActualProvenance60
import R1Z.PV_RunJoin_ResultPost41
/-! An OPEN residual is a success obligation, never a new trust item. This
checks necessity only. It is not a successful run or a ruling-(v) witness. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Open13262
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost41 PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]

theorem no_success {T : Type}
    (law : aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 = .div)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok _ => False)
      (run PV_RunJoin_ActualProvenance60.capture store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store) := by
  unfold run
  apply PV_RunJoin_ResultPost41.bind
  intro reservation
  dsimp only [Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultPost41.bind
  intro status
  cases status with
  | Err e => trivial
  | Ok maskPair =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro cloned
    simp only [aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1,
      law,bind_tc_div]
    trivial

theorem no_capture
    (law : aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 = .div) :
    ∀ p, ¬ PV_RunJoin_ActualProvenance60.Produced p := by
  intro p hp
  obtain ⟨T,store,input,audit,next,hp⟩ := hp
  have h := no_success law store input
  rw [hp] at h
  exact h

#print axioms no_success
#print axioms no_capture
end R1Z.PV_RunJoin_Open13262
