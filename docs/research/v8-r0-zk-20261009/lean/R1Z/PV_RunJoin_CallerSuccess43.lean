import R1Z.PV_RunJoin_CallerDomain43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallerSuccess43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31
theorem success (ops : ExternalFuns) {H T1 T2 : Type}
    (hash : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q)
      (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2)
    (initialHash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H) (nextCommitments : T2)
    (h : @host_semantic.build_with_helper_mode _ (ProverRwP6BodyCandidate.selected ops)
      H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant=
        .ok (.Ok built,nextCommitments)) :
    built.bytes.length=13831 ∧ ∃ records, PV_RunJoin_SemanticDomain40.Domain ops
      (alloc.vec.Vec.deref built.bytes) 27#u8 32#usize 0#u8 records := by
  exact PV_RunJoin_ResultPost41.success _ _ _
    (PV_RunJoin_CallerDomain43.post ops hash helperInst commitInst public1 c1 d g padding
      helper commitments initialHash variant) h
#print axioms success
end R1Z.PV_RunJoin_CallerSuccess43
