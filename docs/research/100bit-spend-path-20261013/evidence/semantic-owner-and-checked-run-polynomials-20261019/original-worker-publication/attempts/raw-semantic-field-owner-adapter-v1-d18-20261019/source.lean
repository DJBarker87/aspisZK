import ExtractedSemanticRoundsCheckedTrace
import ExtractedMaskQM31Exact
import RawExtractedSemanticQM31Ops

/-! A structural adapter from the public-preparation QM31 record to the exact
field.rs extraction reused by the arithmetic-probe proofs.  The public
preparation Aeneas owner supplies the QM31 record type but treats the imported
aspis-core add/mul methods as external; this file therefore names the mapped
source operations explicitly and does not claim that RoundModel.Boundaries is
already instantiated by them. -/
set_option autoImplicit false

namespace AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter

open Aeneas Aeneas.Std Result

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev ProbeQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

/-- Rewrap the same four U32 coordinates in the exact field.rs extraction. -/
def mainToProbe (x : MainQM) : ProbeQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

/-- Inverse coordinate rewrapping into the public-preparation field type. -/
def probeToMain (x : ProbeQM) : MainQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

@[simp] theorem mainToProbe_probeToMain (x : ProbeQM) :
    mainToProbe (probeToMain x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

@[simp] theorem probeToMain_mainToProbe (x : MainQM) :
    probeToMain (mainToProbe x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem main_coordinates_canonical_iff (x : MainQM) :
    Canonical (mainToProbe x) ↔
      x.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      x.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P := by
  rfl

/-- Lift a probe Result through the inverse coordinate isomorphism. -/
def probeResultToMain : Result ProbeQM → Result MainQM
  | .ok x => .ok (probeToMain x)
  | .fail e => .fail e
  | .div => .div

/-- The source-shaped add operation on public-preparation coordinates, using
the byte-pinned field.rs extraction as the operation body. -/
def extractedMainAdd (x y : MainQM) : Result MainQM :=
  probeResultToMain
    (AspisR1SelectedMaskProbe.field.QM31.add (mainToProbe x) (mainToProbe y))

/-- The source-shaped multiply operation on public-preparation coordinates,
using the same pinned field.rs extraction. -/
def extractedMainMul (x y : MainQM) : Result MainQM :=
  probeResultToMain
    (AspisR1SelectedMaskProbe.field.QM31.mul (mainToProbe x) (mainToProbe y))

theorem extractedMainAdd_refines (x y : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y)) :
    ∃ z, extractedMainAdd x y = .ok z ∧ Canonical (mainToProbe z) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe z) =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x) +
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe y) := by
  obtain ⟨z, hz, hcanonical, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      (mainToProbe x) (mainToProbe y) hx hy
  refine ⟨probeToMain z, ?_, ?_, ?_⟩
  · simp [extractedMainAdd, probeResultToMain, hz]
  · simpa using hcanonical
  · simpa using hdecode

theorem extractedMainMul_refines (x y : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y)) :
    ∃ z, extractedMainMul x y = .ok z ∧ Canonical (mainToProbe z) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe z) =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x) *
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe y) := by
  obtain ⟨z, hz, hcanonical, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact
      (mainToProbe x) (mainToProbe y) hx hy
  refine ⟨probeToMain z, ?_, ?_, ?_⟩
  · simp [extractedMainMul, probeResultToMain, hz]
  · simpa using hcanonical
  · simpa using hdecode

#print axioms mainToProbe_probeToMain
#print axioms probeToMain_mainToProbe
#print axioms main_coordinates_canonical_iff
#print axioms extractedMainAdd_refines
#print axioms extractedMainMul_refines

end AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
