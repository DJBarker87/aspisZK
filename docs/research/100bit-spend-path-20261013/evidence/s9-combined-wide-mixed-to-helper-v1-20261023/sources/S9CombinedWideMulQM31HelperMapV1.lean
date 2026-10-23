import S9CombinedWideMulQM31CurrentOuterV1
import S3S9GeneratedWideMulQM31V2
import S3S9ConcreteFieldOpsV1
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CombinedWideMulQM31HelperMapV1

abbrev SrcQ := AspisR1S9GeneratedCombinedQMResultV1.SourceQM
abbrev SrcW := AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact
abbrev CurQ := AspisR1CurrentWide.field.QM31
abbrev CurW := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev HelpQ := AspisR1S9HelperP6.field.QM31
abbrev HelpW := AspisR1S9HelperP6.field.WideExact

abbrev toCurrentQM := AspisR1S9QMSquareCanonicalMapV1.mapQM
abbrev currentToHelperQM := AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
abbrev helperToCurrentQM := AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
def mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

open AspisR1S9CombinedWideMulQM31CurrentOuterV1

def currentToHelperWide (x : CurW) : HelpW :=
  ⟨currentToHelperQM x.c0, currentToHelperQM x.c1⟩

def sourceToHelperQM (q : SrcQ) : HelpQ := currentToHelperQM (toCurrentQM q)

def sourceToHelperWide (x : SrcW) : HelpW :=
  currentToHelperWide (toCurrentWide x)

def sourceToHelperResult (x : SrcW) (q : SrcQ) : Result HelpW :=
  @AspisR1S9HelperP6.FieldOps.wideMulQM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (sourceToHelperWide x) (sourceToHelperQM q)

private theorem mapResult_eq_bind {A B : Type} (f : A → B) (r : Result A) :
    mapResult f r = (do let x ← r; Result.ok (f x)) := by
  cases r <;> rfl

private theorem mapResult_compose {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult (fun x => g (f x)) r = mapResult g (mapResult f r) := by
  cases r <;> rfl

theorem generated_helper_matches_current (x : CurW) (q : CurQ) :
    AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation
        (currentToHelperWide x) (currentToHelperQM q) =
      mapResult currentToHelperWide
        (AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31 x q) := by
  unfold AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation
  change (do
      let out ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31 x q
      Result.ok (currentToHelperWide out)) = _
  rw [mapResult_eq_bind]

private theorem source_result_map_composition (x : SrcW) (q : SrcQ) :
    mapResult sourceToHelperWide
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) =
      mapResult currentToHelperWide
        (mapResult toCurrentWide
          (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q)) := by
  exact mapResult_compose toCurrentWide currentToHelperWide _

theorem combined_wide_mul_qm31_to_helper
    (x : SrcW) (q : SrcQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide x)) :
    mapResult sourceToHelperWide
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) =
      @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (sourceToHelperWide x) (sourceToHelperQM q) := by
  calc
    mapResult sourceToHelperWide
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) =
      mapResult currentToHelperWide
        (mapResult toCurrentWide
          (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q)) :=
        source_result_map_composition x q
    _ = mapResult currentToHelperWide
        (AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
          (toCurrentWide x) (toCurrentQM q)) :=
        congrArg (mapResult currentToHelperWide)
          (combined_wide_mul_qm31_to_current x q hx)
    _ = AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation
        (sourceToHelperWide x) (sourceToHelperQM q) := by
        exact (generated_helper_matches_current (toCurrentWide x) (toCurrentQM q)).symm
    _ = @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (sourceToHelperWide x) (sourceToHelperQM q) := by
        rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMulQM31_dispatch]
        rfl

#print axioms combined_wide_mul_qm31_to_helper

end AspisR1S9CombinedWideMulQM31HelperMapV1
