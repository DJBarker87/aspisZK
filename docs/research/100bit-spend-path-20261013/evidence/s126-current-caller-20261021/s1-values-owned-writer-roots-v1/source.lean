import S1TopWriterPhysicalRootsV1
import S1ValuesOwnedInstallationV1
set_option autoImplicit false
noncomputable section
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result VTop_Stages
open AspisS1TopPrepareSource
variable {CoreError W : Type}

/-- Same writer-prefix conclusion with the complete owned value reference
installed at both compact call sites; no independent value-length premise.
Native correspondence, SDK execution and other Prepared fields remain open. -/
theorem writer_physical_roots (base : Ops) (sourceOps : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (reserved : Bool) (batch : AspisR1.Port3_NativeBatchBody.Ops)
    (geometry : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
    (query : AspisR1.Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : AspisR1.VTop_Provenance.WriterPrefix
      (AspisR1.Port3_NativeWriterShape.installed
        (install base (AspisR1CurrentCaller.S1SemanticInstallation.install
          {(withValues sourceOps) with op10:=AspisS1NativeCompact.compact.expand_semantic nativeValues} R B))
        reserved batch geometry query finish) D hash pub proof split none p a) :
    ∃ (root0 root1 : Array U8 32#usize),
      p.roots=Array.make 2#usize [root0,root1] ∧
      root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 := by
  exact AspisS1TopPrepareSource.writer_physical_roots base (withValues sourceOps) nativeValues R B
    (fun i o s u h => length_frame i o u s h) reserved batch geometry query finish
    D hash pub proof split p a reached

#print axioms writer_physical_roots
end AspisS1ValuesOwnedInstallation
