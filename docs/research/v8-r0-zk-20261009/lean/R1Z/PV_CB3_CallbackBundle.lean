import R1Z.PV_CB3_Op246Coherent
import R1Z.PV_CB3_Op225Coherent
import R1Z.PV_CB3_Op229Source
import R1Z.PV_CB3_Op51Source
import R1Z.PV_CB3_Op120Source
namespace R1Z.PV_CB3_CallbackBundle
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types (base : ExternalTypes) := PV_CB3_Afterstate.selectedTypes base

/-- Compose the four carrier-independent source selections without imposing
any law on the other entries. -/
@[reducible] def four [ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
  PV_CB3_Op246Coherent.selected (PV_CB3_Op225Coherent.selected
    (PV_CB3_Op120Source.selected (PV_CB3_Op51Source.selected ops)))

/-- One dictionary carries all five source equations at the same concrete
extracted afterstate carrier. This does not select a native RunJoin. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (Types base)) : @ExternalFuns (Types base) :=
  @four (Types base) (PV_CB3_Op229Source.selected base ops)

theorem op51_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (x : aspis_core.field.wide_exact.WideExact) :
    @ExternalFuns.op51 (Types base) (selected base ops) x =
      PV_CB3_Op51Source.Raw.wide_bytes_flat x := rfl

theorem op120_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : Array aspis_core.field.QM31 28#usize) :
    @ExternalFuns.op120 (Types base) (selected base ops) p =
      PV_CB3_Op120Source.Raw.boundary_flat p := rfl

theorem op246_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {H : Type} (inst : aspis_core.digest.Digest32 H) (hash : H)
    (left right : Array U8 32#usize) :
    @ExternalFuns.op246 (Types base) (selected base ops) inst hash left right =
      PV_CB3_CoherentOp246.multiproof.binary_parent inst hash left right := rfl

theorem op229_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (a b : @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (Types base)) :
    @ExternalFuns.op229 (Types base) (selected base ops) a b =
      PV_CB3_ShippedOp229.statement_eq (base := base) a b := rfl

theorem op225_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (transfer : @aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 (Types base) →
      PV_CB3_Op225Coherent.Raw.Transfer)
    (withdrawal : @aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 (Types base) →
      PV_CB3_Op225Coherent.Raw.Withdrawal)
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    @ExternalFuns.op225 (Types base) (selected base ops) p =
      @PV_CB3_TransitionExtracted.transition (Types base)
        (@PV_CB3_Op225Coherent.toRaw (Types base) transfer withdrawal p) := by
  cases p <;> rfl

#print axioms op51_source
#print axioms op120_source
#print axioms op246_source
#print axioms op229_source
#print axioms op225_source
end
end R1Z.PV_CB3_CallbackBundle
