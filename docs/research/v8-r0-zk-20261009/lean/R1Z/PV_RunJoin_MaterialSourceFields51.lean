import R1Z.PV_RunJoin_BuildMaterialCircle51
import R1Z.PV_RunJoin_MaterialAlphaProduced51
import R1Z.PV_RunJoin_CircleFields51
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialSourceFields51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T : Type} (D : aspis_core.digest.Digest32 H) (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments nextCommitments : T) (hash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      H T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant=ok (.Ok built,nextCommitments)) :
    (∀ i,i<10 → ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticArray50.raw 10#usize built.alpha i)) ∧
    built.transcript.next_row=27#u8 ∧
    ∃ (before middle : host_wire.SemanticTranscript H) (z0 z1 : aspis_core.circle.SecureCirclePoint)
      (f25 f26 : Slice U8),
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) H D
        before 25#u8 f25=ok (.Ok z0,middle) ∧
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) H D
        middle 26#u8 f26=ok (.Ok z1,built.transcript) ∧
      before.next_row=25#u8 ∧ middle.next_row=26#u8 ∧ built.transcript.hash=before.hash ∧
      built.z=Array.make 2#usize [z0,z1] := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have alpha := PV_RunJoin_MaterialAlphaProduced51.complete base heap box ops D commitInst public1 compiled
    noised maskOnly d g padding commitments nextCommitments hash variant built success
  have circles := PV_RunJoin_BuildMaterialCircle51.complete base heap box ops D commitInst public1 compiled
    noised maskOnly d g padding commitments hash variant
  rw [success] at circles
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz⟩ := circles
  have first := PV_RunJoin_CircleFields51.first D before middle f25 z0 h25
  have second := PV_RunJoin_CircleFields51.second D middle built.transcript f26 z1 h26
  exact ⟨alpha,second.2.2,before,middle,z0,z1,f25,f26,h25,h26,first.1,second.1,
    second.2.1.trans first.2.1,hz⟩
#print axioms complete
end R1Z.PV_RunJoin_MaterialSourceFields51
