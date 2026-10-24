import Port6CK_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Reader
open Aeneas Aeneas.Std Result VTop_Stages
open Port6CK_Semantic (Unwrap)
open CheckpointBytes5Effect

def reader (reserved : Bool) (unwrap : Unwrap) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← Port4A_NativeReader.resume (Port6CK_Ops.ops reserved unwrap)
    (VTop_Checkpoint.digest D) ck proof pub v hash
  match out with
  | .Ok pair => ok (.Ok pair)
  | .Err e => ok (.Err (Port3_CheckpointInstall.error e))

def install (base : Ops) (reserved : Bool) (unwrap : Unwrap) : Ops :=
  {base with op18:=reader reserved unwrap}

theorem size_bound (reserved : Bool) (unwrap : Unwrap)
    (v : AspisR1Stage2.transport.Variant) (n : Usize)
    (returned : (Port6CK_Ops.ops reserved unwrap).checkpointSize v=ok n) : 32≤n.val :=
  Port4A_ReaderInstall.size_bound reserved v n returned

theorem source_success (reserved : Bool) (unwrap : Unwrap) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (ck proof pub : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : reader reserved unwrap D ck proof pub .S2 hash=ok (.Ok (p,a))) :
    Port4A_NativeReader.resume (Port6CK_Ops.ops reserved unwrap)
      (VTop_Checkpoint.digest D) ck proof pub .S2 hash=ok (.Ok (p,a)) := by
  unfold reader at actual
  obtain ⟨returned,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  cases returned with
  | Err e => cases actual
  | Ok pair =>
    have same := core.result.Result.Ok.inj (Result.ok.inj actual)
    cases same
    exact called

/-- SAME physical current op18 return and SAME complete ordered reader log.
This derives retained success; no independent successful reader is assumed. -/
theorem runs (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (ck proof pub : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator) (before : Log)
    (actual : reader reserved unwrap D ck proof pub .S2 hash=ok (.Ok (p,a))) :
    ∃ after,
      run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2) before=ok (.Ok (p,a),after) ∧
      run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) ck proof pub .S2) before=ok (.Ok (p,a),after) := by
  have source := source_success reserved unwrap D hash ck proof pub p a actual
  have erased : erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2)=ok (.Ok (p,a)) := by
    rw [CheckpointBytes5Resume.source,← Port4A_ReaderNormalize.source
      (Port6CK_Ops.ops reserved unwrap) (size_bound reserved unwrap)]
    exact source
  obtain ⟨after,called⟩ := erase_success_run _ _ _ _ erased before
  exact ⟨after,called,Port6CK_Header.accepted reserved unwrap unwrap_ok
    (VTop_Checkpoint.digest D) hash ck proof pub p a before after called⟩

theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (ck proof pub : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : reader reserved unwrap D ck proof pub .S2 hash=ok (.Ok (p,a))) :
    Port4A_ReaderInstall.reader reserved D ck proof pub .S2 hash=ok (.Ok (p,a)) := by
  obtain ⟨after,current,retained⟩ := runs reserved unwrap unwrap_ok D hash ck proof pub p a [] actual
  have erased := run_success _ _ _ _ _ _ retained
  rw [CheckpointBytes5Resume.source] at erased
  have native := (Port4A_ReaderNormalize.source (CheckpointBytes4Ops.ops reserved)
    (Port4A_ReaderInstall.size_bound reserved) (VTop_Checkpoint.digest D) hash ck proof pub .S2).trans erased
  unfold Port4A_ReaderInstall.reader
  rw [native]
  rfl

#print axioms size_bound
#print axioms source_success
#print axioms runs
#print axioms accepted
end AspisR1.Port6CK_Reader
end
