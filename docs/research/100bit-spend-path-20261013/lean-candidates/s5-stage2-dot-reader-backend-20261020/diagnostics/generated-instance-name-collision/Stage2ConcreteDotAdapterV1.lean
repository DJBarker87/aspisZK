import FinishDotReaderLawV1
import Stage2FinishBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2ConcreteDotAdapterV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps
local notation "StageE" => AspisR1Stage2.Stage2Finish.E
local notation "StageK" => AspisR1Stage2.Stage2Finish.K

def toFinishQ (q : StageK) : FinishQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toStageQ (q : FinishQM) : StageK := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toFinishE (x : StageE) : FinishE := ⟨toFinishQ x.c0,toFinishQ x.c1⟩
def toStageE (x : FinishE) : StageE := ⟨toStageQ x.c0,toStageQ x.c1⟩

def mapSlice {A B : Type} (f : A → B) (xs : Slice A) : Slice B :=
  ⟨xs.val.map f,by simpa only [List.length_map] using xs.property⟩

def toStageError : verifier.Error → AspisR1Stage2.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def kernel {W : Type} (ops : FinishOps W PushState) (fm : Slice U8) (ws : Slice StageK) :=
  verifier.finish_query_dot
    (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
      AspisR1EbyKPushDecodedProductUpdate.QRaw) fm (mapSlice toFinishQ ws)

def sourceDot {W : Type} (ops : FinishOps W PushState) (fm : Slice U8) (ws : Slice StageK) :
    Result (core.result.Result StageE AspisR1Stage2.verifier.Error) := do
  let result ← kernel ops fm ws
  match result with
  | .Ok value => ok (.Ok (toStageE value))
  | .Err error => ok (.Err (toStageError error))

def withSourceDot {W S : Type} (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState) : AspisR1Stage2.Stage2Finish.FinishOps S :=
  {stageOps with dot:=sourceDot kernelOps}

theorem roundtrip_finishQ (q : FinishQM) : toFinishQ (toStageQ q)=q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem roundtrip_finishE (x : FinishE) : toFinishE (toStageE x)=x := by
  cases x with | mk c0 c1 => simp only [toStageE,toFinishE,roundtrip_finishQ]

def decodeStage (x : StageE) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeFinish (toFinishE x)

theorem sourceDot_success {W : Type} (ops : FinishOps W PushState)
    (fm : Slice U8) (ws : Slice StageK) (out : StageE)
    (h : sourceDot ops fm ws=ok (.Ok out)) :
    ∃ value : FinishE,kernel ops fm ws=ok (.Ok value) ∧ toStageE value=out := by
  unfold sourceDot at h
  cases hk : kernel ops fm ws with
  | fail error => simp only [hk,bind_tc_fail] at h; cases h
  | div => simp only [hk,bind_tc_div] at h; cases h
  | ok result =>
    cases result with
    | Err error => simp only [hk,bind_tc_ok] at h; cases h
    | Ok value =>
      simp only [hk,bind_tc_ok] at h
      have he := Result.ok.inj h
      exact ⟨value,hk,core.result.Result.Ok.inj he⟩

#print axioms roundtrip_finishQ
#print axioms roundtrip_finishE
#print axioms sourceDot_success
end AspisR1Stage2ConcreteDotAdapterV1
