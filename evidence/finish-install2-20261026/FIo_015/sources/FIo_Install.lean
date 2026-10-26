import FIo_NativeFuns
import FIn_WeightsInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_Install
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
abbrev W := FIn_WeightsInstall.W
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def toQ (q : FIn_WeightsExtract.field.QM31) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toE (x : E) : NE := ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromE (x : NE) : E := ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def variant : FIn_WeightsExtract.FInVariant → FIo_Native.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def toWeights (w : W) : FIo_Native.weights.Weights where
  variant := variant w.variant
  factors := FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray toQ)) w.factors
  points := FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray toQ) w.points
  extra := FIn_WeightsInstall.mapArray toQ w.extra

def toSlice (xs : Slice E) : Slice NE := ⟨xs.val.map toE,by simpa only [List.length_map] using xs.property⟩
def error : FIo_Native.verifier.Error → AspisR1Stage2.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def allocation (r : NP6_StdModel.Reservation) : FIo_Native.Allocation where
  reserve := fun _ before _ => ok (r,before)

/-- Complete retained native Pair body, with coordinate-only adapters and the
same allocator outcome already parameterising the installed top. -/
def pair (r : NP6_StdModel.Reservation) (w : W) (alpha : Slice E)
    (message : Slice U8) (kappa : E) :
    Result (core.result.Result E AspisR1Stage2.verifier.Error) := do
  let result ← @FIo_Native.weights.Weights.pair (allocation r) (toWeights w) (toSlice alpha) message (toE kappa)
  match result with
  | .Ok out => ok (.Ok (fromE out))
  | .Err e => ok (.Err (error e))

def finishOps (r : NP6_StdModel.Reservation) (seed : FinishOps W) : FinishOps W :=
  {FIn_WeightsInstall.install seed with pair:=pair r}

def select {C : Type} (r : NP6_StdModel.Reservation) (c : DrvC_Installation.Configuration W C) :=
  {c with finish:=finishOps r c.finish}

def configuration {C : Type} (err : C) (c : DrvC_Installation.Configuration W C)
    (r : NP6_StdModel.Reservation) := Rc5_Install.configuration err (select r c) r

theorem slots (r : NP6_StdModel.Reservation) (seed : FinishOps W) :
    (finishOps r seed).pair=pair r ∧
    (finishOps r seed).newWeights=FIn_WeightsInstall.newWeights ∧
    (finishOps r seed).field=FIn_Primitives.field ∧
    (finishOps r seed).add=FIn_Primitives.add ∧
    (finishOps r seed).polynomial=FIn_Polynomial.polynomial := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem reached (r : NP6_StdModel.Reservation) (w : W) (alpha : Slice E)
    (message : Slice U8) (kappa out : E)
    (run : pair r w alpha message kappa=ok (.Ok out)) :
    ∃ nativeOut, @FIo_Native.weights.Weights.pair (allocation r)
      (toWeights w) (toSlice alpha) message (toE kappa)=ok (.Ok nativeOut) ∧ fromE nativeOut=out := by
  unfold pair at run
  cases h : @FIo_Native.weights.Weights.pair (allocation r)
      (toWeights w) (toSlice alpha) message (toE kappa) with
  | fail e => simp only [h,bind_tc_fail] at run; cases run
  | div => simp only [h,bind_tc_div] at run; cases run
  | ok result =>
    simp only [h,bind_tc_ok] at run
    cases result with
    | Err e => cases run
    | Ok nativeOut => exact ⟨nativeOut,rfl,core.result.Result.Ok.inj (Result.ok.inj run)⟩

theorem from_to (x : E) : fromE (toE x)=x := rfl

#print axioms slots
#print axioms reached
#print axioms from_to
end AspisR1.FIo_Install
end
