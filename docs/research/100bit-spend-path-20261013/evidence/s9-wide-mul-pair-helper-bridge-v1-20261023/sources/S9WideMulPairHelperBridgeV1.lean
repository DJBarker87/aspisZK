import S9WideFullCurrentSourceV1
import AspisR1S9PairCallerStepV1.Funs
import S9PairCallerStepOperationBridgeV1
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulPairHelperBridgeV1

abbrev Src := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev HelperW := AspisR1S9HelperP6.field.WideExact

private abbrev srcMapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r
private abbrev pairMapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9PairCallerStepOperationBridgeV1.mapResult f r

private theorem pairMapResult_eq_srcMapResult {A B : Type} (f : A → B) :
    pairMapResult f = srcMapResult f := by
  funext r
  cases r <;> rfl

private theorem pairMapResult_comp {A B C : Type} (f : A → B) (g : B → C)
    (r : Result A) :
    pairMapResult g (pairMapResult f r) = pairMapResult (fun x => g (f x)) r := by
  cases r <;> rfl

private theorem pairMapResult_bind {A B : Type} (f : A → B) (r : Result A) :
    pairMapResult f r = (do let x ← r; ok (f x)) := by
  cases r <;> rfl

def srcToPairM (x : AspisR1S9ActualWideMulCutV1.field.M31) :
    AspisR1S9PairCallerStepV1.field.M31 := x

def srcToPairCM (x : AspisR1S9ActualWideMulCutV1.field.CM31) :
    AspisR1S9PairCallerStepV1.field.CM31 := ⟨srcToPairM x.a, srcToPairM x.b⟩

def srcToPairQ (x : AspisR1S9ActualWideMulCutV1.field.QM31) :
    AspisR1S9PairCallerStepV1.field.QM31 := ⟨srcToPairCM x.c0, srcToPairCM x.c1⟩

def srcToPairW (x : Src) : PairW := ⟨srcToPairQ x.c0, srcToPairQ x.c1⟩

def sourceToHelperW (x : Src) : HelperW :=
  AspisR1S9CurrentFieldOpsV1.fromE
    (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)

def pairToHelperW (x : Src) : HelperW :=
  AspisR1S9PairCallerStepV1.toP6W (srcToPairW x)

private theorem helper_carriers_agree (x : Src) :
    pairToHelperW x = sourceToHelperW x := by
  cases x <;> rfl

/-- The exact transparent source `WideExact.mul` result, transported through
its CurrentWide proof and installed helper carriers, is the installed
`concreteFieldOps.wideMul` Result. Canonicality is needed only at the original
checked-arithmetic boundary and is stated at the same four source operands. -/
theorem source_mul_maps_to_installed_helper (x y : Src)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c0)))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c1)))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c0)))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c1))) :
    pairMapResult AspisR1S9PairCallerStepV1.toP6W
      (pairMapResult srcToPairW
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)) =
      @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (pairToHelperW x) (pairToHelperW y) := by
  have hsrc := AspisR1S9WideFullCurrentSourceV1.source_wide_mul_maps_to_current
    x y hx0 hx1 hy0 hy1
  have hsrcPair :
      pairMapResult AspisR1S9WideFullCurrentSourceV1.toCurrentWide
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul
        (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)
        (AspisR1S9WideFullCurrentSourceV1.toCurrentWide y) := by
    rw [pairMapResult_eq_srcMapResult]
    exact hsrc
  have hsrcMapNested :=
    congrArg (pairMapResult AspisR1S9CurrentFieldOpsV1.fromE) hsrcPair
  have hsrcMap :
      pairMapResult
          (AspisR1S9CurrentFieldOpsV1.fromE ∘
            AspisR1S9WideFullCurrentSourceV1.toCurrentWide)
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
        pairMapResult AspisR1S9CurrentFieldOpsV1.fromE
          (AspisR1CurrentWide.field.wide_exact.WideExact.mul
            (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)
            (AspisR1S9WideFullCurrentSourceV1.toCurrentWide y)) := by
    calc
      pairMapResult
          (AspisR1S9CurrentFieldOpsV1.fromE ∘
            AspisR1S9WideFullCurrentSourceV1.toCurrentWide)
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
        pairMapResult AspisR1S9CurrentFieldOpsV1.fromE
          (pairMapResult AspisR1S9WideFullCurrentSourceV1.toCurrentWide
            (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)) := by
              exact (pairMapResult_comp AspisR1S9WideFullCurrentSourceV1.toCurrentWide
                AspisR1S9CurrentFieldOpsV1.fromE _).symm
      _ = pairMapResult AspisR1S9CurrentFieldOpsV1.fromE
          (AspisR1CurrentWide.field.wide_exact.WideExact.mul
            (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)
            (AspisR1S9WideFullCurrentSourceV1.toCurrentWide y)) := hsrcMapNested
  have hcarrier := helper_carriers_agree
  calc
    pairMapResult AspisR1S9PairCallerStepV1.toP6W
        (pairMapResult srcToPairW
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)) =
      pairMapResult (AspisR1S9PairCallerStepV1.toP6W ∘ srcToPairW)
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) :=
          pairMapResult_comp srcToPairW AspisR1S9PairCallerStepV1.toP6W _
    _ = pairMapResult
        (AspisR1S9CurrentFieldOpsV1.fromE ∘
          AspisR1S9WideFullCurrentSourceV1.toCurrentWide)
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) := by
          exact congrArg (fun f => pairMapResult f
            (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y))
            (funext hcarrier)
    _ = pairMapResult AspisR1S9CurrentFieldOpsV1.fromE
        (AspisR1CurrentWide.field.wide_exact.WideExact.mul
          (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)
          (AspisR1S9WideFullCurrentSourceV1.toCurrentWide y)) := hsrcMap
    _ = AspisR1S9ConcreteFieldOpsV1.actualWideMul (sourceToHelperW x) (sourceToHelperW y) := by
          unfold AspisR1S9ConcreteFieldOpsV1.actualWideMul sourceToHelperW
          rw [AspisR1S9CurrentFieldOpsV1.to_from,
            AspisR1S9CurrentFieldOpsV1.to_from]
          exact (pairMapResult_bind AspisR1S9CurrentFieldOpsV1.fromE
            (AspisR1CurrentWide.field.wide_exact.WideExact.mul
              (AspisR1S9WideFullCurrentSourceV1.toCurrentWide x)
              (AspisR1S9WideFullCurrentSourceV1.toCurrentWide y)))
    _ = @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (pairToHelperW x) (pairToHelperW y) := by
          rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMul_dispatch,
            ← helper_carriers_agree, ← helper_carriers_agree]

/-- The pair caller's actual `field.WideExact.mul` slot and the exact source
WideExact.mul cut produce the same installed helper Result on structurally
corresponding operands. This is the call-site boundary used by the S2-only
`weights.factored_s2_libra_weights` body. -/
theorem pair_mul_matches_source_mul (x y : Src)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c0)))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c1)))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c0)))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c1))) :
    pairMapResult AspisR1S9PairCallerStepV1.toP6W
      (AspisR1S9PairCallerStepV1.field.WideExact.mul (srcToPairW x) (srcToPairW y)) =
      pairMapResult AspisR1S9PairCallerStepV1.toP6W
        (pairMapResult srcToPairW
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)) := by
  calc
    pairMapResult AspisR1S9PairCallerStepV1.toP6W
        (AspisR1S9PairCallerStepV1.field.WideExact.mul (srcToPairW x) (srcToPairW y)) =
      @AspisR1S9HelperP6.FieldOps.wideMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9PairCallerStepV1.toP6W (srcToPairW x))
        (AspisR1S9PairCallerStepV1.toP6W (srcToPairW y)) :=
          AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul
            (srcToPairW x) (srcToPairW y)
    _ = pairMapResult AspisR1S9PairCallerStepV1.toP6W
        (pairMapResult srcToPairW
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)) := by
          symm
          exact source_mul_maps_to_installed_helper x y hx0 hx1 hy0 hy1

#print axioms source_mul_maps_to_installed_helper
#print axioms pair_mul_matches_source_mul

end AspisR1S9WideMulPairHelperBridgeV1
