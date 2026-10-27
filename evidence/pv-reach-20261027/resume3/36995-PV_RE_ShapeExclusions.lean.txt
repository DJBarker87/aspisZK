import R1Z.PV_RE_ExcludedPoison
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ShapeExclusions
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_ShapePoison
variable [ExternalTypes]
/-- All seven excluded fields preserve every extracted transfer Result,
without an admission or success hypothesis. This is Result invariance. -/
theorem transfer {C : Type} (D : ExternalFuns)
    (entry : PV_RE_ExcludedPoison.ExcludedField) (e : Error)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    @RealR1_client.prove_for_proof_accounts _ (PV_RE_ExcludedPoison.poison D entry e) C
      entropy (.Transfer p transition) compiled hash store state =
    @RealR1_client.prove_for_proof_accounts _ D C
      entropy (.Transfer p transition) compiled hash store state := by
  rw [PV_RE_ExcludedPoison.unchanged]

/-- The same seven replacement laws for every extracted withdrawal input. -/
theorem withdrawal {C : Type} (D : ExternalFuns)
    (entry : PV_RE_ExcludedPoison.ExcludedField) (e : Error)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    @RealR1_client.prove_for_proof_accounts _ (PV_RE_ExcludedPoison.poison D entry e) C
      entropy (.Withdrawal p transition) compiled hash store state =
    @RealR1_client.prove_for_proof_accounts _ D C
      entropy (.Withdrawal p transition) compiled hash store state := by
  rw [PV_RE_ExcludedPoison.unchanged]

#print axioms transfer
#print axioms withdrawal
end R1Z.PV_RE_ShapeExclusions
