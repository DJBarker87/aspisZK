import R1Z.PV_RunJoin_WeightAbsorb66
import R1Z.PV_RunJoin_CallerDomain43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticMaterialDomain66
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem helper (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) {H T1 T2 : Type}
    (hash : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q)
      (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2)
    (initialHash : H) (variant : transport.Variant) :
    Post (fun next : (core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error) × T2 =>
      match next.1 with
      | .Err _ => True
      | .Ok built => built.bytes.length=13831 ∧ ∃ records, @PV_RunJoin_SemanticDomain40.Domain (types base) (selected base heap box ops)
          (alloc.vec.Vec.deref built.bytes) 27#u8 32#usize 0#u8 records)
      (@host_semantic.build_with_helper_mode (types base) (selected base heap box ops)
        H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant) := by
  have h := @PV_RunJoin_CallerDomain43.post (types base) (selected base heap box ops)
    H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant
  rw [PV_RunJoin_WeightAbsorb66.complete base heap box ops] at h
  exact h
#print axioms helper

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T : Type} (D : aspis_core.digest.Digest32 H) (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments : T) (hash : H) (variant : transport.Variant) :
    Post (fun pair =>
      match pair.1 with
      | .Err _ => True
      | .Ok built =>
        built.bytes.length=13831 ∧ ∃ records, @PV_RunJoin_SemanticDomain40.Domain (types base)
          (selected base heap box ops) (alloc.vec.Vec.deref built.bytes) 27#u8 32#usize 0#u8 records)
      (@host_semantic.build_with_material (types base) (selected base heap box ops)
        H T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold host_semantic.build_with_material
  simp only [lift,bind_tc_ok]
  split
  · trivial
  · split
    · trivial
    · apply PV_RunJoin_ResultPost41.bind
      intro transition
      apply PV_RunJoin_ResultPost41.bind
      intro different
      cases different with
      | true => trivial
      | false =>
        simp only [Bool.false_eq_true,if_false,lift,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro columns
        exact helper base heap box ops D
          (host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error D commitInst)
          commitInst public1 columns d g padding (compiled,public1) commitments hash variant

#print axioms complete
end R1Z.PV_RunJoin_SemanticMaterialDomain66
