import Tx1Q_QueryBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_PrefixInstall
open Tx1Q_Carriers

def topError : VTop_Stages.verifier.Error → AspisR1CurrentCaller.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def topResult {A B : Type} (f : A → B)
    (m : Result (core.result.Result A VTop_Stages.verifier.Error)) :
    Result (core.result.Result B AspisR1CurrentCaller.verifier.Error) := do
  let r ← m
  match r with
  | .Ok a => ok (.Ok (f a))
  | .Err err => ok (.Err (topError err))

theorem top_success {A B : Type} (f : A → B) (g : B → A)
    (roundtrip : ∀ a, g (f a) = a)
    (m : Result (core.result.Result A VTop_Stages.verifier.Error)) (out : B)
    (success : topResult f m = ok (.Ok out)) : m = ok (.Ok (g out)) := by
  cases m with
  | fail err => cases success
  | div => cases success
  | ok r =>
    cases r with
    | Err err => cases success
    | Ok a =>
      have eq := core.result.Result.Ok.inj (Result.ok.inj success)
      subst out
      rw [roundtrip]

def initial (reserved : Bool) (v : AspisR1CurrentCaller.transport.Variant) :=
  topResult unAccumulator (Port3_Initial.constructor reserved (variant v))

def newPending (reserved : Bool) (weights : Slice C.K) :=
  topResult unPending (Port3_NativePendingInstall.source reserved (slice k weights))

def unGeometry (g : S.G) : C.G := ⟨g.start,g.inverses,g.line_z⟩

def geometryBody {CoreError : Type} (ops : Port3_NativeGeometryBody.Ops CoreError)
    (queries : Array U32 22#usize) (start stop : Usize) :=
  topResult unGeometry
    (Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install ops) queries start stop)

/-- Source helper choices needed to derive the ten-step prefix, in addition
 to the requested query/flush/writer choices. Preparation and batch stay intact. -/
def install {CoreError : Type} (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError) :
    AspisR1CurrentCaller.Ops :=
  {Tx1Q_Install.install base (Tx1Q_QueryBridge.leaves queryOps) with
    op20 := initial reserved, op18 := newPending reserved, op19 := geometryBody geoOps}

theorem other_slots {CoreError : Type} (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError) :
    {install base reserved queryOps geoOps with op7 := base.op7, op17 := base.op17,
      op16 := base.op16, op20 := base.op20, op18 := base.op18, op19 := base.op19} = base := by
  cases base; rfl

theorem initial_success (reserved : Bool) (out : C.A)
    (success : initial reserved .S2 = ok (.Ok out)) :
    Port3_Initial.constructor reserved .S2 = ok (.Ok (accumulator out)) :=
  top_success unAccumulator accumulator accumulator_roundtrip _ _ success

theorem pending_success (reserved : Bool) (weights : Slice C.K) (out : C.B)
    (success : newPending reserved weights = ok (.Ok out)) :
    Port3_NativePendingInstall.source reserved (slice k weights) = ok (.Ok (pending out)) :=
  top_success unPending pending pending_roundtrip _ _ success

theorem geometry_success {CoreError : Type} (ops : Port3_NativeGeometryBody.Ops CoreError)
    (queries : Array U32 22#usize) (start stop : Usize) (out : C.G)
    (success : geometryBody ops queries start stop = ok (.Ok out)) :
    Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install ops) queries start stop =
      ok (.Ok (geometry out)) :=
  top_success unGeometry geometry (by intro g; cases g; rfl) _ _ success

#print axioms top_success
#print axioms other_slots
#print axioms initial_success
#print axioms pending_success
#print axioms geometry_success
end AspisR1.Tx1Q_PrefixInstall
end
