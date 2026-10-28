import NDO_JHc_WriterTotal
import NDO_JGr_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_InstalledWriter
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Actual WAdm op16 returns on this materialized accumulator. The bytes are
chosen by the source writer and digest, not by an external checkpoint. -/
theorem source (p : verifier.Prepared) (out : verifier.Accumulator)
    (flushed : Slice aspis_core.field.QM31)
    (variant : p.variant=.S2) (next : out.next.val=10) (size : flushed.val.length=64) :
    ∃ saved, installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved ∧ saved.val.length=1768 := by
  let a : verifier.Accumulator := {out with weights:=⟨flushed.val,flushed.property⟩}
  let pp := CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p)
  let aa := CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator a)
  let D := VTop_Checkpoint.digest (Tx1Q_Install.digest digest)
  have total : ∀ parts, ∃ value, D.digest () parts=ok value := by
    intro parts
    exact ⟨_,rfl⟩
  have asize : aa.weights.val.length=64 := by
    simpa only [aa,a,CheckpointBytes3Namespaces.toAccumulator,CheckpointBytes3Namespaces.mapVec,
      Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,List.length_map] using size
  have pvariant : pp.variant=.S2 := by
    change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  have anext : aa.next.val=10 := next
  obtain ⟨saved,run,length⟩ := JHc_WriterTotal.code_total D () total pp aa
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput asize pvariant anext
  refine ⟨⟨saved.val,saved.property⟩,?_,length⟩
  change WAdm_SourceWriter.writer (Tx1Q_Install.digest digest)
    (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator a)
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=_
  unfold WAdm_SourceWriter.writer
  rw [run,bind_tc_ok]
#print axioms source
end AspisR1.JHc_InstalledWriter
end
