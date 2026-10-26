import FIn_WeightsFuns
import FIn_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_WeightsInstall
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
abbrev W := FIn_WeightsExtract.Weights

def toQ (q : K) : FIn_WeightsExtract.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toPoint (z : aspis_core.circle.SecureCirclePoint) : FIn_WeightsExtract.circle.SecureCirclePoint :=
  ⟨toQ z.x,toQ z.y⟩
def mapArray {A B : Type} {n : Usize} (f : A → B) (a : Array A n) : Array B n :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def variant : transport.Variant → FIn_WeightsExtract.FInVariant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def newWeights (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) :
    Result (core.result.Result W verifier.Error) := do
  let result ← FIn_WeightsExtract.weights_new (variant v) (mapArray toQ alpha) (mapArray toPoint z)
  match result with
  | .Ok w => ok (.Ok w)
  | .Err .Allocation => ok (.Err .Allocation)

def install (seed : FinishOps W) : FinishOps W :=
  {FIn_Install.finishOps seed with newWeights := newWeights}

theorem slot (seed : FinishOps W) : (install seed).newWeights=newWeights := rfl

theorem retained_pair (seed : FinishOps W) : (install seed).pair=seed.pair := rfl

theorem same_call (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : W)
    (run : FIn_WeightsExtract.weights_new (variant v) (mapArray toQ alpha) (mapArray toPoint z)=ok (.Ok w)) :
    newWeights v alpha z=ok (.Ok w) := by
  simp only [newWeights,run,bind_tc_ok]

def select {C : Type} (c : DrvC_Installation.Configuration W C) :=
  {c with finish:=install c.finish}

def configuration {C : Type} (err : C) (c : DrvC_Installation.Configuration W C)
    (r : NP6_StdModel.Reservation) := Rc5_Install.configuration err (select c) r

theorem finish {C : Type} (err : C) (c : DrvC_Installation.Configuration W C)
    (r : NP6_StdModel.Reservation) : (configuration err c r).finish=install c.finish := rfl

#print axioms finish
#print axioms slot
#print axioms retained_pair
#print axioms same_call
end AspisR1.FIn_WeightsInstall
end
