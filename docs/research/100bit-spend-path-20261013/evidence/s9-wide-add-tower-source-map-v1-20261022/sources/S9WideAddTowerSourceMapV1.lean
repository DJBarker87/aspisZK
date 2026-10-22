import S9WideAddCMSourceMapV1
import S3S9CurrentFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideAddTowerSourceMapV1

abbrev SourceCM := AspisR1S9WideAddSourceBodyV1.field.CM31
abbrev SourceQM := AspisR1S9WideAddSourceBodyV1.field.QM31
abbrev SourceWide := AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact
abbrev CurrentCM := AspisR1CurrentWide.field.CM31
abbrev CurrentQM := AspisR1CurrentWide.field.QM31
abbrev CurrentWide := AspisR1CurrentWide.field.wide_exact.WideExact

abbrev CMCanonical := AspisR1S9WideAddCMSourceMapV1.CMCanonical

def QMCanonical (x : SourceQM) : Prop :=
  CMCanonical x.c0 ∧ CMCanonical x.c1

def WideCanonical (x : SourceWide) : Prop :=
  QMCanonical x.c0 ∧ QMCanonical x.c1

def toCurrentCM := AspisR1S9WideAddCMSourceMapV1.toCurrentCM
def toCurrentQM (x : SourceQM) : CurrentQM :=
  ⟨toCurrentCM x.c0, toCurrentCM x.c1⟩
def toCurrentWide (x : SourceWide) : CurrentWide :=
  ⟨toCurrentQM x.c0, toCurrentQM x.c1⟩

def toHelperCM (x : SourceCM) : AspisR1S9HelperP6.field.CM31 := ⟨x.a,x.b⟩
def toHelperQM (x : SourceQM) : AspisR1S9HelperP6.field.QM31 :=
  ⟨toHelperCM x.c0,toHelperCM x.c1⟩
def toHelperWide (x : SourceWide) : AspisR1S9HelperP6.field.WideExact :=
  ⟨toHelperQM x.c0,toHelperQM x.c1⟩

theorem source_wide_canonical_iff_current (x : SourceWide) :
    WideCanonical x ↔
      AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide x) := by
  rfl

theorem source_wide_canonical_iff_helper (x : SourceWide) :
    WideCanonical x ↔
      AspisR1S9CurrentFieldOpsV1.Canonical (toHelperWide x) := by
  rfl

theorem source_qm_add_maps_to_current
    (x y : SourceQM) (hx : QMCanonical x) (hy : QMCanonical y) :
    ∃ z : SourceQM,
      AspisR1S9WideAddSourceBodyV1.field.QM31.add x y = .ok z ∧
      AspisR1CurrentWide.field.QM31.add (toCurrentQM x) (toCurrentQM y) =
        .ok (toCurrentQM z) := by
  obtain ⟨c0, hs0, hc0⟩ :=
    AspisR1S9WideAddCMSourceMapV1.source_cm_add_maps_to_current
      x.c0 y.c0 hx.1 hy.1
  obtain ⟨c1, hs1, hc1⟩ :=
    AspisR1S9WideAddCMSourceMapV1.source_cm_add_maps_to_current
      x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨c0,c1⟩, ?_, ?_⟩
  · simp only [AspisR1S9WideAddSourceBodyV1.field.QM31.add,
      hs0, hs1, bind_tc_ok]
  · change (do
      let c ← AspisR1CurrentWide.field.CM31.add
        (toCurrentCM x.c0) (toCurrentCM y.c0)
      let c1 ← AspisR1CurrentWide.field.CM31.add
        (toCurrentCM x.c1) (toCurrentCM y.c1)
      ok ({ c0 := c, c1 := c1 } : CurrentQM)) =
        .ok ({ c0 := toCurrentCM c0, c1 := toCurrentCM c1 } : CurrentQM)
    simp only [toCurrentCM, AspisR1S9WideAddCMSourceMapV1.toCurrentCM] at hc0 hc1 ⊢
    simp only [hc0, hc1, bind_tc_ok]

theorem source_wide_add_maps_to_current
    (x y : SourceWide) (hx : WideCanonical x) (hy : WideCanonical y) :
    ∃ z : SourceWide,
      AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact.add x y = .ok z ∧
      AspisR1CurrentWide.field.wide_exact.WideExact.add
        (toCurrentWide x) (toCurrentWide y) = .ok (toCurrentWide z) := by
  obtain ⟨q0, hs0, hc0⟩ :=
    source_qm_add_maps_to_current x.c0 y.c0 hx.1 hy.1
  obtain ⟨q1, hs1, hc1⟩ :=
    source_qm_add_maps_to_current x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨q0,q1⟩, ?_, ?_⟩
  · simp only [AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact.add,
      hs0, hs1, bind_tc_ok]
  · change (do
      let q ← AspisR1CurrentWide.field.QM31.add
        (toCurrentQM x.c0) (toCurrentQM y.c0)
      let q1 ← AspisR1CurrentWide.field.QM31.add
        (toCurrentQM x.c1) (toCurrentQM y.c1)
      ok ({ c0 := q, c1 := q1 } : CurrentWide)) =
        .ok ({ c0 := toCurrentQM q0, c1 := toCurrentQM q1 } : CurrentWide)
    simp only [hc0, hc1, bind_tc_ok]

#print axioms source_wide_canonical_iff_current
#print axioms source_wide_canonical_iff_helper
#print axioms source_qm_add_maps_to_current
#print axioms source_wide_add_maps_to_current

end AspisR1S9WideAddTowerSourceMapV1
