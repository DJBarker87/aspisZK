import RPu_FJo_AlphaPersistence
import RPu_FJo_Tx1AlphaCanonical
import RPz7_SdkD_CheckpointBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_NativeReader
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Literal alpha transport on the original native writer/reader operands. -/
theorem alpha {CoreError Hash : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) (base : VTop_Stages.Ops)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (checkpoint proof1 pub1 : Slice U8) (p1 : AspisR1Stage2.verifier.Prepared)
    (a1 : AspisR1Stage2.verifier.Accumulator)
    (same : MultiproofConeCanonical.bytesOf checkpoint.val=MultiproofConeCanonical.bytesOf saved.val)
    (reader : Port4A_ReaderInstall.reader reserved (Tx1Q_Install.digest D) checkpoint proof1 pub1 .S2 hash=ok (.Ok (p1,a1)))
    (literal : AspisWideTower.WideExact)
    (literal0 : ∀ a0,Array.index_usize (Tx1Q_Carriers.prepared run.p).alpha 0#usize=ok a0 →
      CheckpointBytes5Output.ofE a0=literal)
    (alpha1 : AspisR1Stage2.Stage2Finish.E) (read1 : Array.index_usize p1.alpha 0#usize=ok alpha1) :
    CheckpointBytes5Output.ofE alpha1=literal := by
  let p0 := Tx1Q_Carriers.prepared run.p
  obtain ⟨alpha0,read0,cell⟩ := WP.spec_imp_exists (Array.index_usize_spec p0.alpha 0#usize
    (by change (0#usize).val<p0.alpha.val.length;rw [p0.alpha.property];decide))
  have canonical := FJo_Tx1AlphaCanonical.value ops reserved query geo B std D hash pub publicBytes proof split saved run alpha0 read0
  have source := Port4A_ReaderInstall.accepted_source base reserved (Tx1Q_Install.digest D) hash
    checkpoint proof1 pub1 .S2 p1 a1 reader
  have equal := FJo_AlphaPersistence.value reserved (Tx1Q_Install.digest D) p0 p1
    (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) a1
    checkpoint proof publicBytes proof1 pub1 hash saved alpha0 alpha1 read0 read1 canonical run.writer_call same source
  exact equal.trans (literal0 alpha0 read0)
#print axioms alpha
end AspisR1.FJp_NativeReader
end
