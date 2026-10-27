import Port4A_ReaderNormalize
import Port3_NativeWriterShape
import Port3_CheckpointRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_ReaderInstall
open Aeneas Aeneas.Std Result VTop_Stages

theorem mul_value (x y : Usize) (h : x.val*y.val≤65536) :
    x*y=ok (Usize.ofNat (x.val*y.val) (by scalar_tac)) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x:=x) (y:=y) (by scalar_tac))
  have same : z=Usize.ofNat (x.val*y.val) (by scalar_tac) := by
    apply UScalar.eq_of_val_eq
    simpa using hv
  simpa only [same] using hz

theorem add_value (x y : Usize) (h : x.val+y.val≤65536) :
    x+y=ok (Usize.ofNat (x.val+y.val) (by scalar_tac)) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have same : z=Usize.ofNat (x.val+y.val) (by scalar_tac) := by
    apply UScalar.eq_of_val_eq
    simpa using hv
  simpa only [same] using hz

theorem size_bound (reserved : Bool) (v : AspisR1Stage2.transport.Variant) (n : Usize)
    (h : (CheckpointBytes4Ops.ops reserved).checkpointSize v=ok n) : 32≤n.val := by
  cases v <;>
    simp only [CheckpointBytes4Ops.ops,CheckpointBytes4Ops.checkpointSize,
      CheckpointBytes4Ops.finalLen,bind_tc_ok] at h <;>
    rw [mul_value _ _ (by decide),bind_tc_ok,add_value _ _ (by decide)] at h <;>
    cases Result.ok.inj h <;> decide

def reader (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← Port4A_NativeReader.resume (CheckpointBytes4Ops.ops reserved)
    (VTop_Checkpoint.digest D) ck proof pub v hash
  match out with
  | .Ok pair => ok (.Ok pair)
  | .Err e => ok (.Err (Port3_CheckpointInstall.error e))

theorem reference_eq (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    reader reserved D ck proof pub v hash =
      Port3_CheckpointInstall.reader reserved D ck proof pub v hash := by
  unfold reader Port3_CheckpointInstall.reader
  rw [Port4A_ReaderNormalize.source _ (size_bound reserved)]
  rfl

def install (base : Ops) (reserved : Bool) : Ops :=
  {base with op18 := reader reserved}

theorem accepted_source (base : Ops) (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (ck proof pub : Slice U8)
    (v : transport.Variant) (p : verifier.Prepared) (a : verifier.Accumulator)
    (h : (install base reserved).op18 D ck proof pub v hash=ok (.Ok (p,a))) :
    AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest D) ck proof pub v hash=ok (.Ok (p,a)) := by
  change reader reserved D ck proof pub v hash=_ at h
  rw [reference_eq] at h
  exact Port3_CheckpointInstall.reader_success reserved D ck proof pub v hash p a h

#print axioms mul_value
#print axioms add_value
#print axioms size_bound
#print axioms reference_eq
#print axioms accepted_source
end AspisR1.Port4A_ReaderInstall
end
