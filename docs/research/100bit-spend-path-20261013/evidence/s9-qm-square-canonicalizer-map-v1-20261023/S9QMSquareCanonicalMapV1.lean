import AspisR1S9SquareMulQMCutV1.Funs
import S3S9GeneratedWideMulQM31V2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareCanonicalMapV1

abbrev CutM := AspisR1S9SquareMulQMCutV1.field.M31
abbrev CutCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev CutQ := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev CurM := AspisR1CurrentWide.field.M31
abbrev CurCM := AspisR1CurrentWide.field.CM31
abbrev CurQ := AspisR1CurrentWide.field.QM31

def mapM (x : CutM) : CurM := x
def mapCM (x : CutCM) : CurCM := ⟨mapM x.a, mapM x.b⟩
def mapQM (x : CutQ) : CurQ := ⟨mapCM x.c0, mapCM x.c1⟩

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    mapResult f (Bind.bind r k) = Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl

theorem canonical_word_eq (i : CutM) :
    AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () i =
    AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () i := by
  unfold AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
    AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
    AspisR1S9SquareMulQMCutV1.field.P AspisR1CurrentWide.field.P
  rfl

theorem canonical_qm31_result_map (q : CutQ) :
    mapResult mapQM
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31 q) =
    AspisR1CurrentWide.field.wide_exact.canonical_qm31 (mapQM q) := by
  unfold AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31
    AspisR1CurrentWide.field.wide_exact.canonical_qm31
  simp only [mapResult_bind, canonical_word_eq, mapQM, mapCM, mapM, bind_tc_ok]
  rfl

#print axioms canonical_word_eq
#print axioms canonical_qm31_result_map

end AspisR1S9QMSquareCanonicalMapV1
