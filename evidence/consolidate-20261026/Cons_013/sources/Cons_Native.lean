import T2Nat_NativePair
set_option autoImplicit false
noncomputable section
namespace AspisR1.Cons_Native
open Aeneas Aeneas.Std Result
structure Witness where
  p2 : AspisR1Stage2.verifier.Prepared
  saved2 : AspisR1Stage2.verifier.Accumulator
  g2 : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize
  geometry2 : AspisR1Stage2.verifier.QueryGeometry
  pending2 : AspisR1Stage2.verifier.BatchedWeights
  returned2 : AspisR1Stage2.verifier.Accumulator
  after2 : AspisR1Stage2.verifier.BatchedWeights
  flushed2 : Slice AspisR1Stage2.aspis_core.field.QM31
  back2 : Slice AspisR1Stage2.aspis_core.field.QM31 → alloc.vec.Vec AspisR1Stage2.aspis_core.field.QM31
  v2 : AspisR1Stage2.verifier.View

def Calls {F CoreError Hash : Type} (base : VTop_Stages.Ops)
    (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Witness) : Prop :=
      (Tx2N_Execution.control base reserved queryOps geoOps).op18 D checkpoint proof pub .S2 hash = ok (.Ok (t.p2,t.saved2)) ∧
      T2Nat_ReaderJoin.reader reserved D checkpoint proof pub .S2 hash = ok (.Ok (t.p2,t.saved2)) ∧
      checkpoint.val.length = 1768 ∧ reserved = true ∧
      T2Nat_ReaderEffects.OnRun reserved D () checkpoint proof pub t.p2 t.saved2 ∧
      (Tx2N_Execution.control base reserved queryOps geoOps).op6 proof t.p2 t.saved2 t.g2 none t.geometry2 t.pending2 22#usize = ok (.Ok (t.returned2,t.after2)) ∧
      alloc.vec.Vec.deref_mut t.returned2.weights = (t.returned2.weights.deref,t.back2) ∧
      (Tx2N_Execution.control base reserved queryOps geoOps).op9 t.after2 t.returned2.weights.deref = ok t.flushed2 ∧
      let a := {t.returned2 with weights := t.back2 t.flushed2}
      (Tx2I_Install.stage (Op5T_Concrete.stage (Tx2N_Execution.control base reserved queryOps geoOps)) finishOps).op19 t.v2 t.p2 a none = ok (.Ok ()) ∧
      Port4D_FinishInstall.finish finishOps t.v2 t.p2 a none = ok (.Ok ()) ∧
      (∀ {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
        (before : CheckpointBytes5Effect.Log),
        CheckpointBytes5Effect.run D hash
          (T2Nat_Silent.code (T2Nat_FinishResult.installed finishOps t.v2 t.p2 a)) before =
          ok (.Ok (),before))

end AspisR1.Cons_Native
end
