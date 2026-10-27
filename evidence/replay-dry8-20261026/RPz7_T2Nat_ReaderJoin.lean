import T2Nat_TailJoin
import T2Nat_ResumePrefix
import RPz7_Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

theorem header (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : H)
    (consume : T2Nat_ResumePrefix.Tail) :
    T2Nat_ResumePrefix.body (T2Nat_ReaderOps.ops reserved) D bytes proof pub v hash consume =
      T2Nat_ResumePrefix.body (CheckpointBytes4Ops.ops reserved) D bytes proof pub v hash consume := rfl

theorem resume (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    EqOk (Port4A_NativeReader.resume (T2Nat_ReaderOps.ops reserved) D bytes proof pub v hash)
      (Port4A_NativeReader.resume (CheckpointBytes4Ops.ops reserved) D bytes proof pub v hash) := by
  rw [← T2Nat_ResumePrefix.source,← T2Nat_ResumePrefix.source,header]
  exact T2Nat_ResumePrefix.congr _ D bytes proof pub v hash _ _
    (T2Nat_TailJoin.source reserved bytes v)

/-- Concrete op18 source body, with the exact caller error adapter. Native
codecs/iterator are substituted; no whole reader result is an input. -/
def reader (reserved : Bool) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : VTop_Stages.transport.Variant) (hash : H) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) VTop_Stages.verifier.Error) := do
  let out ← Port4A_NativeReader.resume (T2Nat_ReaderOps.ops reserved)
    (VTop_Checkpoint.digest D) bytes proof pub v hash
  match out with
  | .Ok pair => ok (.Ok pair)
  | .Err e => ok (.Err (Port3_CheckpointInstall.error e))

theorem reader_eq (reserved : Bool) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : VTop_Stages.transport.Variant) (hash : H) :
    EqOk (reader reserved D bytes proof pub v hash)
      (Port4A_ReaderInstall.reader reserved D bytes proof pub v hash) := by
  unfold reader Port4A_ReaderInstall.reader
  exact T2Nat_ResultEq.bind (resume reserved (VTop_Checkpoint.digest D) bytes proof pub v hash)
    (fun _ => T2Nat_ResultEq.refl _)

/-- Same retained bytes, same returned Prepared/Accumulator, derived physical
length and actual allocation admission. Nothing is selected independently. -/
theorem on_run (base : VTop_Stages.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (bytes proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : (Tx2N_Install.inner base reserved query).op18 D bytes proof pub .S2 hash = ok (.Ok (p,a))) :
    reader reserved D bytes proof pub .S2 hash = ok (.Ok (p,a)) ∧
    bytes.val.length = 1768 ∧ reserved = true := by
  have current : Port4A_ReaderInstall.reader reserved D bytes proof pub .S2 hash = ok (.Ok (p,a)) := actual
  have native := (reader_eq reserved D bytes proof pub .S2 hash _).mpr current
  have original := Tx2N_Install.reader_success base reserved query D hash bytes proof pub .S2 p a actual
  obtain ⟨magic,zeros,next,iterator,rest,size,other⟩ :=
    Tx2N_Header.cuts reserved (VTop_Checkpoint.digest D) bytes proof pub hash p a original
  exact ⟨native,size,CheckpointBytes4Ops.successful_reservation reserved
    (VTop_Checkpoint.digest D) bytes proof pub .S2 hash p a original⟩

#print axioms header
#print axioms resume
#print axioms reader_eq
#print axioms on_run
end AspisR1.T2Nat_ReaderJoin
end
