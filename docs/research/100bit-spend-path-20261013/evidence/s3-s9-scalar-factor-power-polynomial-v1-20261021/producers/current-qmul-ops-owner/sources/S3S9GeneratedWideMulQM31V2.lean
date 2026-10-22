import CurrentWideField
import S3S9CurrentFieldOpsV1
import KpowersCurrentQMSemanticsV1
import S3S9CurrentWideMulQM31V1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

/- The exact declaration cut emitted from the pinned `field/wide_exact.rs`
    method. `CurrentWideField` provides the exact carrier and concrete source
    `field.QM31.mul`; these four definitions are the nonempty v2 extraction
    bodies reintroduced under their emitted names. -/
namespace AspisR1CurrentWide

abbrev field.wide_exact.canonical_qm31.closure := Unit

def field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
  (c : field.wide_exact.canonical_qm31.closure) (tupled_args : field.M31) : Result field.M31 := do
  let i ← tupled_args % field.P
  ok i

def field.wide_exact.canonical_qm31 (value : field.QM31) : Result field.QM31 := do
  let m ← field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () value.c0.a
  let m1 ← field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () value.c0.b
  let m2 ← field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () value.c1.a
  let m3 ← field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () value.c1.b
  ok { c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } }

def field.wide_exact.WideExact.mul_qm31
    (self : field.wide_exact.WideExact) (rhs : field.QM31) : Result field.wide_exact.WideExact := do
  let rhs1 ← field.wide_exact.canonical_qm31 rhs
  let q ← field.QM31.mul self.c0 rhs1
  let q1 ← field.QM31.mul self.c1 rhs1
  ok { c0 := q, c1 := q1 }

def wide_mul_qm31
    (x : field.wide_exact.WideExact) (y : field.QM31) : Result field.wide_exact.WideExact := do
  field.wide_exact.WideExact.mul_qm31 x y

end AspisR1CurrentWide

namespace AspisR1S9GeneratedWideMulQM31V2

abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev W := AspisR1S9HelperP6.field.WideExact

def toQM (x : Q) : AspisR1CurrentWide.field.QM31 :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def toWide (x : W) : AspisR1CurrentWide.field.wide_exact.WideExact :=
  ⟨toQM x.c0, toQM x.c1⟩

private def fromQM (x : AspisR1CurrentWide.field.QM31) : Q :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private def fromWide (x : AspisR1CurrentWide.field.wide_exact.WideExact) : W :=
  ⟨fromQM x.c0, fromQM x.c1⟩

def actualHelperOperation (x : W) (q : Q) : Result W := do
  let out ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
    (toWide x) (toQM q)
  ok (fromWide out)

@[reducible] def installActualQm31 (ops : AspisR1S9HelperP6.FieldOps) : AspisR1S9HelperP6.FieldOps :=
  { ops with wideMulQM31 := actualHelperOperation }

theorem generated_helper_dispatch (x : W) (q : Q) :
    (letI : AspisR1S9HelperP6.FieldOps := installActualQm31 AspisR1S9HelperP6PowerSemanticsV1.currentQMOps
     AspisR1S9HelperP6.field.WideExact.mul_qm31 x q) = actualHelperOperation x q := by
  rfl

private def sourceModel (x : W) (q : Q) : Result W :=
  do
    let a ← q.c0.a % (2147483647#u32)
    let b ← q.c0.b % (2147483647#u32)
    let c ← q.c1.a % (2147483647#u32)
    let d ← q.c1.b % (2147483647#u32)
    let rhs : Q := ⟨⟨a,b⟩,⟨c,d⟩⟩
    let p0 ← AspisR1CurrentWide.field.QM31.mul (toQM x.c0) (toQM rhs)
    let p1 ← AspisR1CurrentWide.field.QM31.mul (toQM x.c1) (toQM rhs)
    ok (fromWide ⟨p0,p1⟩)

theorem sourceModel_eq_currentSource (x : W) (q : Q) :
    sourceModel x q = AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source x q := by
  rfl

theorem actualHelperOperation_eq_sourceModel (x : W) (q : Q) :
    actualHelperOperation x q = sourceModel x q := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk x00 x01 =>
      cases c1 with
      | mk x10 x11 =>
        cases q with
        | mk q0 q1 =>
          cases q0 with
          | mk q00 q01 =>
            cases q1 with
            | mk q10 q11 =>
              simp [actualHelperOperation, sourceModel, toQM, toWide,
                fromQM, fromWide,
                AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31,
                AspisR1CurrentWide.field.wide_exact.canonical_qm31,
                AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
                AspisR1CurrentWide.field.P]


theorem actualHelperOperation_success (x : W) (q : Q) (z : W)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM (toQM q))
    (h : actualHelperOperation x q = .ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide (toWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (toWide z) =
        ⟨AspisR1CurrentWide.Proof.decodeQM (toQM x.c0) *
            AspisR1CurrentWide.Proof.decodeQM (toQM q),
          AspisR1CurrentWide.Proof.decodeQM (toQM x.c1) *
            AspisR1CurrentWide.Proof.decodeQM (toQM q)⟩ := by
  have hs : AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source x q = .ok z := by
    rw [← sourceModel_eq_currentSource]
    exact (actualHelperOperation_eq_sourceModel x q).symm.trans h
  have hx' : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide x) := by
    simpa [toWide, toQM, AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hx
  have hq' : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q) := by
    simpa [toQM, AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hq
  have hout := AspisR1S9HelperP6PowerSemanticsV1.currentWideMulQM31Source_success
    x q z hx' hq' hs
  simpa [toWide, toQM, AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide,
    AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM] using hout


#print axioms actualHelperOperation_eq_sourceModel
#print axioms generated_helper_dispatch
#print axioms actualHelperOperation_success

end AspisR1S9GeneratedWideMulQM31V2
