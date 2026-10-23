import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9SquareMulQMCutV1.Funs
import S9PairCallerStepOperationBridgeV1
import S9QMSquareHelperSourceBridgeV1
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairQMSquareToSourceV1

abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev SrcQ := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev HelperQ := AspisR1S9HelperP6.field.QM31

local instance currentFieldOpsForSemantics : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

def pairToSrcCM (x : AspisR1S9PairCallerStepV1.field.CM31) :
    AspisR1S9SquareMulQMCutV1.field.CM31 := ⟨x.a, x.b⟩

def pairToSrcQ (x : PairQ) : SrcQ :=
  ⟨pairToSrcCM x.c0, pairToSrcCM x.c1⟩

def srcToPairCM (x : AspisR1S9SquareMulQMCutV1.field.CM31) :
    AspisR1S9PairCallerStepV1.field.CM31 := ⟨x.a, x.b⟩

def srcToPairQ (x : SrcQ) : PairQ :=
  ⟨srcToPairCM x.c0, srcToPairCM x.c1⟩

private theorem pair_input_to_source (x : PairQ) :
    AspisR1S9QMSquareHelperSourceBridgeV1.toCut
      (AspisR1S9PairCallerStepV1.toP6Q x) = pairToSrcQ x := by
  cases x with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

private theorem source_output_to_pair (x : SrcQ) :
    AspisR1S9PairCallerStepV1.toP6Q (srcToPairQ x) =
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut x := by
  cases x with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

private theorem pairToP6Q_injective :
    Function.Injective AspisR1S9PairCallerStepV1.toP6Q := by
  intro x y h
  have h' := congrArg AspisR1S9PairCallerStepV1.fromP6Q h
  rw [AspisR1S9PairCallerStepV1.fromP6Q_toP6Q,
    AspisR1S9PairCallerStepV1.fromP6Q_toP6Q] at h'
  exact h'

private theorem mapResult_comp {A B C : Type} (g : B → C) (f : A → B)
    (r : Result A) :
    AspisR1S9PairCallerStepOperationBridgeV1.mapResult g
      (AspisR1S9PairCallerStepOperationBridgeV1.mapResult f r) =
    AspisR1S9PairCallerStepOperationBridgeV1.mapResult (g ∘ f) r := by
  cases r <;> rfl

private theorem mapResult_injective {A B : Type} (f : A → B)
    (hf : Function.Injective f) (r s : Result A)
    (h : AspisR1S9PairCallerStepOperationBridgeV1.mapResult f r =
      AspisR1S9PairCallerStepOperationBridgeV1.mapResult f s) : r = s := by
  cases r with
  | ok x => cases s with
    | ok y => exact congrArg Result.ok (hf (Result.ok.inj h))
    | fail e => cases h
    | div => cases h
  | fail e => cases s with
    | ok y => cases h
    | fail e' => cases Result.fail.inj h; rfl
    | div => cases h
  | div => cases s with
    | ok y => cases h
    | fail e => cases h
    | div => rfl

/-- The exact frozen Pair-caller square call maps to the extracted source-cut
square on the same operand, after the explicit Pair→P6→cut carrier maps. The
only semantic hypothesis is the installed current-QM canonicality needed by
the checked square seam. This is a full Result equality. -/
theorem pair_qm_square_maps_to_source
    (x : PairQ)
    (hx : AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.canonical
      (AspisR1S9PairCallerStepV1.toP6Q x)) :
    AspisR1S9PairCallerStepV1.field.QM31.square x =
      AspisR1S9PairCallerStepOperationBridgeV1.mapResult srcToPairQ
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x)) := by
  have hpair := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square x
  have hsource :=
    AspisR1S9QMSquareHelperSourceBridgeV1.actual_qm_square_maps_to_installed_helper
      (AspisR1S9PairCallerStepV1.toP6Q x) hx
  have hsource' : AspisR1S9PairCallerStepOperationBridgeV1.mapResult
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x)) =
      AspisR1S9ConcreteFieldOpsV1.actualQMSquare
        (AspisR1S9PairCallerStepV1.toP6Q x) := by
    rw [← pair_input_to_source x]
    change AspisR1S9PairCallerStepOperationBridgeV1.mapResult
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q x))) = _
    exact hsource
  have hmapper :
      AspisR1S9PairCallerStepV1.toP6Q ∘ srcToPairQ =
        AspisR1S9QMSquareHelperSourceBridgeV1.fromCut := by
    funext z
    exact source_output_to_pair z
  have hcomposed : AspisR1S9PairCallerStepOperationBridgeV1.mapResult
      AspisR1S9PairCallerStepV1.toP6Q
      (AspisR1S9PairCallerStepOperationBridgeV1.mapResult srcToPairQ
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x))) =
      @AspisR1S9HelperP6.FieldOps.qmSquare
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9PairCallerStepV1.toP6Q x) := by
    calc
      _ = AspisR1S9PairCallerStepOperationBridgeV1.mapResult
        (AspisR1S9PairCallerStepV1.toP6Q ∘ srcToPairQ)
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x)) :=
          mapResult_comp _ _ _
      _ = AspisR1S9PairCallerStepOperationBridgeV1.mapResult
        AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x)) := by
          rw [hmapper]
      _ = AspisR1S9ConcreteFieldOpsV1.actualQMSquare
        (AspisR1S9PairCallerStepV1.toP6Q x) := by
          change AspisR1S9PairCallerStepOperationBridgeV1.mapResult
            AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
            (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x)) = _
          exact hsource'
      _ = @AspisR1S9HelperP6.FieldOps.qmSquare
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9PairCallerStepV1.toP6Q x) :=
          (AspisR1S9ConcreteFieldOpsV1.concrete_qmSquare_dispatch
            (AspisR1S9PairCallerStepV1.toP6Q x)).symm
  have hresult : AspisR1S9PairCallerStepOperationBridgeV1.mapResult
      AspisR1S9PairCallerStepV1.toP6Q
      (AspisR1S9PairCallerStepV1.field.QM31.square x) =
      AspisR1S9PairCallerStepOperationBridgeV1.mapResult
        AspisR1S9PairCallerStepV1.toP6Q
        (AspisR1S9PairCallerStepOperationBridgeV1.mapResult srcToPairQ
          (AspisR1S9SquareMulQMCutV1.field.QM31.square (pairToSrcQ x))) :=
    hpair.trans hcomposed.symm
  exact mapResult_injective AspisR1S9PairCallerStepV1.toP6Q
    pairToP6Q_injective _ _ hresult

#print axioms pair_qm_square_maps_to_source

end AspisR1S9PairQMSquareToSourceV1
