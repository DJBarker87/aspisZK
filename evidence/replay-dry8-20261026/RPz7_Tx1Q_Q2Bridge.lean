import RPz7_Tx1Q_SameCut
import Port5Q2_Checkpoint
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Q2Bridge
open Tx1Q_Carriers

/-- Nominal error transport commutes for every outer and inner Result. -/
theorem result_factor {A B : Type} (f : A → B)
    (m : Result (core.result.Result A AspisR1Stage2.verifier.Error)) :
    Tx1Q_Install.result f m = Tx1Q_PrefixInstall.topResult f (Port3_QueryInstall.result m) := by
  cases m with
  | fail err => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Ok a => rfl
    | Err err => cases err <;> rfl

/-- Q2's query slot becomes Q1's exact installed body by choosing its leaf
instance explicitly. No whole-dictionary agreement predicate is assumed. -/
theorem query {CoreError W : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (queryOps : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (proof : Slice U8) (p : C.P) (a : C.A) (g : Array C.E 29#usize)
    (geo : C.G) (b : C.B) (stop : Usize) :
    Tx1Q_Install.query (Tx1Q_QueryBridge.leaves queryOps) proof p a g none geo b stop =
    Tx1Q_PrefixInstall.topResult (fun x : S.A × S.B => (unAccumulator x.1,unPending x.2))
      ((Port5Q2_Checkpoint.installed base reserved batch geoOps
        (Port5Q1_QueryPorts.install (Port3_QueryStage.release queryOps)) finish).op6
        proof (prepared p) (accumulator a) (arr e g) none (geometry geo) (pending b) stop) := by
  unfold Tx1Q_Install.query
  rw [result_factor]
  rfl

/-- Q2 op9 is the same retained mutable flush, with reversible QM31 maps. -/
theorem flush {CoreError W : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (queryOps : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (b : C.B) (old : Slice C.K) :
    Tx1Q_Install.flush b old = (do
      let out ← (Port5Q2_Checkpoint.installed base reserved batch geoOps queryOps finish).op9
        (pending b) (slice k old)
      ok (slice unK out)) := rfl

/-- Q2 op8 is definitionally the same writer REFERENCE, not an unproved
claim that the shipped native writer accepts every input in this carrier. -/
theorem writer {CoreError W H : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (queryOps : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (p : C.P) (a : C.A) (proof pub : Slice U8) :
    Tx1Q_Install.writer D p a proof pub hash =
      (Port5Q2_Checkpoint.installed base reserved batch geoOps queryOps finish).op8
        (Tx1Q_Install.digest D) (prepared p) (accumulator a) proof pub hash := rfl

#print axioms result_factor
#print axioms query
#print axioms flush
#print axioms writer
end AspisR1.Tx1Q_Q2Bridge
end
