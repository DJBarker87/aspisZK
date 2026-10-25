import T2Nat_ResumeCode
import T2Nat_ReaderJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderEffects
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Effect T2Nat_CodeEq T2Nat_ResultEq

theorem header (reserved : Bool) (bytes proof pub : Slice U8) (v : transport.Variant)
    (consume : T2Nat_ResumePrefix.Tail) :
    T2Nat_ResumeCode.body (T2Nat_ReaderOps.ops reserved) bytes proof pub v consume =
      T2Nat_ResumeCode.body (CheckpointBytes4Ops.ops reserved) bytes proof pub v consume := rfl

/-- Native helper substitution preserves the SAME full returned value and
ordered oracle log, for arbitrary initial histories and every returned error. -/
theorem program (reserved : Bool) (bytes proof pub : Slice U8) (v : transport.Variant) :
    EqRun (CheckpointBytes5Resume.program (T2Nat_ReaderOps.ops reserved) bytes proof pub v)
      (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub v) := by
  rw [← T2Nat_ResumeCode.source,← T2Nat_ResumeCode.source,header]
  apply T2Nat_ResumeCode.congr
  intro next finish checksum digest
  change EqOk
    (Port4A_NativeReader.tail (T2Nat_ReaderOps.ops reserved) bytes v next finish checksum digest)
    (Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes v next finish checksum digest)
  exact T2Nat_TailJoin.source reserved bytes v next finish checksum digest

/-- Full erasure association to the emitted wrapping parent; its checked
subtraction is justified by the actual length guard, including rejected runs. -/
theorem source (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (hash : H) (bytes proof pub : Slice U8) (v : transport.Variant) :
    erase D hash (CheckpointBytes5Resume.program (T2Nat_ReaderOps.ops reserved) bytes proof pub v) =
      Port4A_NativeReader.resume (T2Nat_ReaderOps.ops reserved) D bytes proof pub v hash := by
  have normal := Port4A_ReaderNormalize.source (T2Nat_ReaderOps.ops reserved)
    (Port4A_ReaderInstall.size_bound reserved) D hash bytes proof pub v
  exact (CheckpointBytes5Resume.source (T2Nat_ReaderOps.ops reserved) D bytes proof pub v hash).trans normal.symm

def OnRun (reserved : Bool) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (hash : H) (bytes proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) : Prop :=
  ∀ before : Log, ∃ after : Log,
    run (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Resume.program (T2Nat_ReaderOps.ops reserved) bytes proof pub .S2)
      before = ok (.Ok (p,a),after) ∧
    run (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2)
      before = ok (.Ok (p,a),after)

/-- Both effects are derived from the exact installed op18 call. A second
accepted run or a freely chosen source log is never a hypothesis. -/
theorem on_run (base : VTop_Stages.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (bytes proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : (Tx2N_Install.inner base reserved query).op18 D bytes proof pub .S2 hash = ok (.Ok (p,a))) :
    OnRun reserved D hash bytes proof pub p a := by
  intro before
  have original := Tx2N_Install.reader_success base reserved query D hash bytes proof pub .S2 p a actual
  have erased := (CheckpointBytes5Resume.source (CheckpointBytes4Ops.ops reserved)
    (VTop_Checkpoint.digest D) bytes proof pub .S2 hash).trans original
  obtain ⟨after,call⟩ := Port3_CheckpointInstall.erase_success_run
    (VTop_Checkpoint.digest D) hash _ _ erased before
  refine ⟨after,?_,call⟩
  exact (program reserved bytes proof pub .S2 (VTop_Checkpoint.digest D) hash before _).mpr call

#print OnRun
#print axioms header
#print axioms program
#print axioms source
#print axioms on_run
end AspisR1.T2Nat_ReaderEffects
end
