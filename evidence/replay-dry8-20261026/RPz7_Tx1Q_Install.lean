import RPz7_Tx1Q_Carriers
import Port3_FlushInstall
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Install
open Tx1Q_Carriers

def result {A B : Type} (f : A → B)
    (m : Result (core.result.Result A AspisR1Stage2.verifier.Error)) :
    Result (core.result.Result B AspisR1CurrentCaller.verifier.Error) := do
  let r ← m
  match r with
  | .Ok a => ok (.Ok (f a))
  | .Err err => ok (.Err (error err))

def query (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (p : C.P) (a : C.A) (g : Array C.E 29#usize)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (geo : C.G) (b : C.B) (stop : Usize) :=
  result (fun x : S.A × S.B => (unAccumulator x.1,unPending x.2))
    (Port3_NativeQueryBody.verifier.candidate.query_loop (Port3_QueryStage.release ops)
      proof (prepared p) (accumulator a) (arr e g) (observer obs) (geometry geo) (pending b) stop)

def flush (b : C.B) (old : Slice C.K) : Result (Slice C.K) := do
  let out ← Port3_FlushInstall.flush (pending b) (slice k old)
  ok (slice unK out)

def digest {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) :
    VTop_Stages.aspis_core.digest.Digest32 H := ⟨D.coremarkerCopyInst,D.digest⟩

/-- This is the existing selector writer reference; its bounded native P6
certificate is separate. No assertion of unconditional native adoption. -/
def writer {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (p : C.P) (a : C.A) (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) :=
  Port3_CheckpointInstall.writer (digest D) (prepared p) (accumulator a) proof pub hash

/-- CurrentCaller slots 7/17/16 are VTop query6/flush9/writer8. -/
def install (base : AspisR1CurrentCaller.Ops) (ops : Port3_NativeQueryBody.Ops) :
    AspisR1CurrentCaller.Ops :=
  {base with op7 := query ops, op17 := flush, op16 := writer}

theorem other_slots (base : AspisR1CurrentCaller.Ops) (ops : Port3_NativeQueryBody.Ops) :
    {install base ops with op7 := base.op7, op17 := base.op17, op16 := base.op16} = base := by
  cases base; rfl

theorem installed_slots (base : AspisR1CurrentCaller.Ops) (ops : Port3_NativeQueryBody.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    let actual := RowShape_InstalledSlots.verifierOps (install base ops) B std
    actual.op7 = query ops ∧ actual.op17 = flush ∧ @actual.op16 = @writer := by
  exact ⟨rfl,rfl,rfl⟩

theorem query_success (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (p : C.P) (a out : C.A) (g : Array C.E 29#usize)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (geo : C.G) (b bout : C.B) (stop : Usize)
    (success : query ops proof p a g obs geo b stop = ok (.Ok (out,bout))) :
    Port3_NativeQueryBody.verifier.candidate.query_loop (Port3_QueryStage.release ops)
      proof (prepared p) (accumulator a) (arr e g) (observer obs) (geometry geo) (pending b) stop =
      ok (.Ok (accumulator out,pending bout)) := by
  unfold query result at success
  generalize call : Port3_NativeQueryBody.verifier.candidate.query_loop
    (Port3_QueryStage.release ops) proof (prepared p) (accumulator a) (arr e g)
      (observer obs) (geometry geo) (pending b) stop = r at success ⊢
  cases r with
  | fail err => cases success
  | div => cases success
  | ok r =>
    cases r with
    | Err err => cases success
    | Ok pair =>
      cases pair with
      | mk x y =>
        have eq := core.result.Result.Ok.inj (Result.ok.inj success)
        cases eq
        simp only [accumulator_roundtrip,pending_roundtrip]

theorem flush_success (b : C.B) (old out : Slice C.K)
    (success : flush b old = ok out) :
    Port3_FlushInstall.flush (pending b) (slice k old) = ok (slice k out) := by
  unfold flush at success
  generalize call : Port3_FlushInstall.flush (pending b) (slice k old) = r at success ⊢
  cases r with
  | fail err => cases success
  | div => cases success
  | ok s =>
    have eq := Result.ok.inj success
    subst out
    simp [slice,List.map_map,Function.comp_def]

#print axioms other_slots
#print axioms installed_slots
#print axioms query_success
#print axioms flush_success
end AspisR1.Tx1Q_Install
end
