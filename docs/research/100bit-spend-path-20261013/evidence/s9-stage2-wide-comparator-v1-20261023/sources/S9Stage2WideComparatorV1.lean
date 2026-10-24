import CurrentWideEqSemanticV7
import Stage2FinishBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Stage2WideComparatorV1
abbrev SW := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev CW := AspisR1CurrentWide.field.wide_exact.WideExact
/-- Literal eight-coordinate adapter; no normalization or arithmetic. -/
def toCurrent (x : SW) : CW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromCurrent (x : CW) : SW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem coordinate_roundtrip (x : SW) : fromCurrent (toCurrent x)=x := by rfl
/-- The emitted derived Eq body already proved in CurrentWideEqSemanticV7,
followed by default PartialEq.ne's Boolean negation. Correspondence of the
external Stage2 Eq slot to this body remains a separately pinned source port. -/
def sourceNe (x y : SW) : Result Bool := do
  let equal ← AspisR1CurrentWide.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
    (toCurrent x) (toCurrent y)
  ok (!equal)
/-- Accepted false inequality implies source structural equality for every
field carrier, without canonicality, decoder or arithmetic premises. -/
theorem source_ne_false_eq (x y : SW) (h : sourceNe x y=.ok false) : x=y := by
  unfold sourceNe at h
  cases he : AspisR1CurrentWide.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
      (toCurrent x) (toCurrent y) with
  | fail e => simp only [he,bind_tc_fail] at h; cases h
  | div => simp only [he,bind_tc_div] at h; cases h
  | ok equal =>
    simp only [he,bind_tc_ok] at h
    cases equal with
    | false => cases h
    | true =>
      have hxy := AspisR1CurrentWide.wide_partialEq_success_true (toCurrent x) (toCurrent y) he
      have hm := congrArg fromCurrent hxy
      simpa only [coordinate_roundtrip] using hm

def installComparator {W : Type} (ops : AspisR1Stage2.Stage2Finish.FinishOps W) :
    AspisR1Stage2.Stage2Finish.FinishOps W := {ops with ne:=sourceNe}
#print axioms coordinate_roundtrip
#print axioms source_ne_false_eq
end AspisR1S9Stage2WideComparatorV1
