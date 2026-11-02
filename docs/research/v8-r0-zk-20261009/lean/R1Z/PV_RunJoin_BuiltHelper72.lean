import R1Z.PV_RunJoin_MaterialBackendBalanced72
import R1Z.PV_RunJoin_LiftRows72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuiltHelper72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
abbrev Q := aspis_core.field.QM31

def Balanced [ExternalTypes] [ExternalFuns] {H : Type} (built : host_semantic.BuiltSemantics H) : Prop :=
  ∃ h o q,Array.index_usize built.columns 26#usize=ok h ∧
    aspis_statement.state_only_semantic.state_only_copy_helper_sum (alloc.vec.Vec.deref h)=ok o ∧
    aspis_core.field.QM31.ZERO=ok q ∧
    core.option.Option.Insts.CoreCmpPartialEqOption.eq aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      o (some q)=ok true

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T : Type} (D : aspis_core.digest.Digest32 H) (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments next : T) (hash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      H T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant=ok (.Ok built,next)) :
    @Balanced (types base) (selected base heap box ops) H built := by
  have traced := PV_RunJoin_MaterialBackendBalanced72.complete base heap box ops D commitInst
    public1 compiled noised maskOnly d g padding commitments hash variant
  erw [success] at traced
  obtain ⟨columns,lengths,first,root1,root2,h,hs,hfirst,hsecond,lifted,o,q,ho,hq,heq⟩ := traced
  exact ⟨h,o,q,PV_RunJoin_LiftRows72.helper base heap box ops columns lengths h g d built.columns lifted,ho,hq,heq⟩

#print axioms Balanced
#print axioms complete
end R1Z.PV_RunJoin_BuiltHelper72
