import CurrentFinishField
import AspisR1WeightsPairCutEbyKDotOpsV1
import EbyKPowerValueCanonicalToPushV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutFieldCallbackV1

abbrev PairWide := AspisR1WeightsPairCut.field.WideExact
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE

/-- Coordinate-only carrier map from the retained parser/finish record to the
nominal WideExact type emitted for Weights::pair. -/
def finishToPair (x : FinishE) : PairWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

/-- Concrete callback built from the retained checked decoder. This is a
source-model callback; its identification with PairCut's external declaration
is an explicit source-correspondence obligation. -/
def checkedFieldCallback (bytes : Slice U8) (i : Usize) : Result PairWide := do
  let x ← AspisR1CurrentWide.Proof.finishField bytes i
  ok (finishToPair x)

theorem finishToPair_maps_current_wide (x : FinishE) :
    AspisR1EbyKPowerValueCanonicalToPush.pushToSource
      (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource (finishToPair x)) =
      AspisR1CurrentWide.Proof.toMinimalWide
        (AspisR1CurrentWide.Proof.ofFinishE x) := by
  rfl

theorem checkedFieldCallback_success_push_canonical
    (bytes : Slice U8) (i : Usize) (out : PairWide)
    (h : checkedFieldCallback bytes i = .ok out) :
    AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource out) := by
  unfold checkedFieldCallback at h
  cases hf : AspisR1CurrentWide.Proof.finishField bytes i with
  | fail e => simp only [hf, bind_tc_fail] at h; cases h
  | div => simp only [hf, bind_tc_div] at h; cases h
  | ok x =>
    simp only [hf, bind_tc_ok] at h
    have hout : finishToPair x = out := Result.ok.inj h
    subst out
    have hc := AspisR1CurrentWide.Proof.finishField_success_canonical bytes i x hf
    have hc' : AspisR1CurrentWideMul.CanonicalWide
        (AspisR1CurrentWide.Proof.toMinimalWide
          (AspisR1CurrentWide.Proof.ofFinishE x)) := hc
    change AspisR1CurrentWideMul.CanonicalWide
      (AspisR1EbyKPowerValueCanonicalToPush.pushToSource
        (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource (finishToPair x)))
    rw [finishToPair_maps_current_wide]
    exact hc'

#print axioms finishToPair_maps_current_wide
#print axioms checkedFieldCallback_success_push_canonical
end AspisR1S5PairCutFieldCallbackV1
