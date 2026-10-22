import AspisR1S9HelperP6.Funs
import KpowersCurrentQMSemanticsV1
import S3S9CurrentFieldOpsV1
import S3S9GeneratedWideMulQM31V2
import TransparentFoldRangeLawV1
import ExtractedMaskQM31SquareExact
import CurrentWideMulExactProduct

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteFieldOpsV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev M := AspisR1S9HelperP6.field.M31

private def toSelectedQM (x : Q) : AspisR1SelectedMaskProbe.field.QM31 :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private def fromSelectedQM (x : AspisR1SelectedMaskProbe.field.QM31) : Q :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem selected_roundtrip (x : Q) : fromSelectedQM (toSelectedQM x) = x := by
  cases x <;> rfl

def actualQMSquare (x : Q) : Result Q := do
  let z ← AspisR1SelectedMaskProbe.field.QM31.square (toSelectedQM x)
  ok (fromSelectedQM z)

def actualWideMul (x y : W) : Result W := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul
    (AspisR1S9CurrentFieldOpsV1.toE x) (AspisR1S9CurrentFieldOpsV1.toE y)
  ok (AspisR1S9CurrentFieldOpsV1.fromE z)

def actualWideAdd (x y : W) : Result W :=
  AspisR1S9CurrentFieldOpsV1.actualWideAdd x y

def actualWideMulM31 (x : W) (s : M) : Result W :=
  AspisR1S9CurrentFieldOpsV1.actualWideMulM31 x s

def actualWideMulQM31 (x : W) (q : Q) : Result W :=
  AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation x q

@[reducible] def concreteFieldOps : Ops :=
  let base : Ops := {
    AspisR1S9HelperP6PowerSemanticsV1.currentQMOps with
    qmSquare := actualQMSquare
    wideMul := actualWideMul
    wideAdd := actualWideAdd
    wideMulM31 := actualWideMulM31
    wideMulQM31 := actualWideMulQM31
  }
  AspisR1S9TransparentFoldRangeLawV1.installExtractedFold base

instance concreteFieldOpsInstance : Ops := concreteFieldOps

theorem concrete_qmMul_is_current (x y : Q) :
    @AspisR1S9HelperP6.FieldOps.qmMul concreteFieldOps x y =
      @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9HelperP6PowerSemanticsV1.currentQMOps x y := rfl

theorem kpowers_concrete_eq_current (n : Std.Usize) (x : Q) :
    @AspisR1S9HelperP6.weights.kpowers concreteFieldOps n x =
      @AspisR1S9HelperP6.weights.kpowers
        AspisR1S9HelperP6PowerSemanticsV1.currentQMOps n x := rfl

theorem concrete_qmSquare_dispatch (x : Q) :
    @AspisR1S9HelperP6.FieldOps.qmSquare concreteFieldOps x = actualQMSquare x := rfl

theorem concrete_wideAdd_dispatch (x y : W) :
    @AspisR1S9HelperP6.FieldOps.wideAdd concreteFieldOps x y = actualWideAdd x y := rfl

theorem concrete_wideMulM31_dispatch (x : W) (s : M) :
    @AspisR1S9HelperP6.FieldOps.wideMulM31 concreteFieldOps x s = actualWideMulM31 x s := rfl

theorem concrete_wideMulQM31_dispatch (x : W) (q : Q) :
    @AspisR1S9HelperP6.FieldOps.wideMulQM31 concreteFieldOps x q = actualWideMulQM31 x q := rfl

theorem concrete_wideMul_dispatch (x y : W) :
    @AspisR1S9HelperP6.FieldOps.wideMul concreteFieldOps x y = actualWideMul x y := rfl

theorem concrete_iterFold_law :
    AspisR1S9HelperP6.IteratorFoldRangeP6Law concreteFieldOps := by
  exact AspisR1S9TransparentFoldRangeLawV1.installed_extracted_fold_satisfies_P6 _

theorem actualWideMul_total_exact (x y : W)
    (hx : AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hy : AspisR1S9CurrentFieldOpsV1.Canonical y) :
    ∃ z, actualWideMul x y = .ok z ∧
      AspisR1S9CurrentFieldOpsV1.Canonical z ∧
      AspisR1S9CurrentFieldOpsV1.decode z =
        AspisR1S9CurrentFieldOpsV1.decode x * AspisR1S9CurrentFieldOpsV1.decode y := by
  obtain ⟨z,hz,hc,hv⟩ := AspisR1CurrentWide.Proof.wide_mul_total_exact
    (AspisR1S9CurrentFieldOpsV1.toE x) (AspisR1S9CurrentFieldOpsV1.toE y) hx hy
  refine ⟨AspisR1S9CurrentFieldOpsV1.fromE z, ?_, ?_, ?_⟩
  · simp [actualWideMul,hz]
  · change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE z))
    rw [AspisR1S9CurrentFieldOpsV1.to_from]
    exact hc
  · change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE z)) = _
    rw [AspisR1S9CurrentFieldOpsV1.to_from]
    exact hv

#print axioms concrete_qmMul_is_current
#print axioms kpowers_concrete_eq_current
#print axioms concrete_qmSquare_dispatch
#print axioms concrete_wideAdd_dispatch
#print axioms concrete_wideMulM31_dispatch
#print axioms concrete_wideMulQM31_dispatch
#print axioms concrete_wideMul_dispatch
#print axioms concrete_iterFold_law
#print axioms actualWideMul_total_exact

end AspisR1S9ConcreteFieldOpsV1
