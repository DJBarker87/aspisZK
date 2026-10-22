import AspisR1S9WideAddSourceBodyV1.Funs
import S9WideAddCanonicalMapV4
import CurrentWideLinearExact

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideAddCMSourceMapV1

abbrev P : Nat := AspisR1.ExtractedCurrentM31AddSub.P
abbrev SourceCM := AspisR1S9WideAddSourceBodyV1.field.CM31
abbrev CurrentCM := AspisR1CurrentWide.field.CM31

def toCurrentCM (x : SourceCM) : CurrentCM := ⟨x.a, x.b⟩
def M31Canonical (x : Std.U32) : Prop := x.val < P
def CMCanonical (x : SourceCM) : Prop := M31Canonical x.a ∧ M31Canonical x.b

theorem source_cm_add_maps_to_current
    (x y : SourceCM) (hx : CMCanonical x) (hy : CMCanonical y) :
    ∃ z : SourceCM,
      AspisR1S9WideAddSourceBodyV1.field.CM31.add x y = .ok z ∧
      AspisR1CurrentWide.field.CM31.add (toCurrentCM x) (toCurrentCM y) =
        .ok (toCurrentCM z) := by
  obtain ⟨a, hsa, hca⟩ :=
    AspisR1S9WideAddCanonicalMapV4.source_m31_add_maps_to_current
      x.a y.a hx.1 hy.1
  obtain ⟨b, hsb, hcb⟩ :=
    AspisR1S9WideAddCanonicalMapV4.source_m31_add_maps_to_current
      x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩, ?_, ?_⟩
  · simp only [AspisR1S9WideAddSourceBodyV1.field.CM31.add,
      hsa, hsb, bind_tc_ok]
  · change (do
      let m ← AspisR1CurrentWide.field.M31.add x.a y.a
      let m1 ← AspisR1CurrentWide.field.M31.add x.b y.b
      ok ({ a := m, b := m1 } : AspisR1CurrentWide.field.CM31)) =
        .ok ({ a := a, b := b } : AspisR1CurrentWide.field.CM31)
    simp only [hca, hcb, bind_tc_ok]

#print axioms source_cm_add_maps_to_current

end AspisR1S9WideAddCMSourceMapV1
