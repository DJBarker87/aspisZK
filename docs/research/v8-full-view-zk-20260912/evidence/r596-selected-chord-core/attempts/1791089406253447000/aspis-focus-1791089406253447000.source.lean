import AspisV8R19.R595CoreChordScaling
import AspisV8R19.R203ChordDataExecution
import AspisV8R17.NormalizedChord

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R596SelectedChordCore
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core AspisV8R15.ExactTowerBase
open R165QuarticExecution (Canonical decode)
open R164ProductExecution (encode)
open R203ChordDataExecution R574SparseGCorePolynomial R595CoreChordScaling
open AspisV8R17
noncomputable section
local instance : NeZero (2 : QM31Exact) := ⟨AspisV8R15.ExactTowerChord.two_ne_zero⟩

theorem selected_rawData_core (s z : circle.SecureCirclePoint)
    (hsx : Canonical s.x) (hsy : Canonical s.y)
    (hzx : Canonical z.x) (hzy : Canonical z.y) (hsz : s ≠ z)
    (u v half alpha b0 b1 again : QM31Exact)
    (hu : 1+u^2 ≠ 0) (hv : 1+v^2 ≠ 0) (hne : v ≠ u)
    (hx0 : decode s.x = rationalX u) (hy0 : decode s.y = rationalY u)
    (hx1 : decode z.x = rationalX v) (hy1 : decode z.y = rationalY v) :
    ∃ data : ChordData,
      rawData s z (encode b0) (encode b1) (encode again) = .ok (.Ok data) ∧
      data.abc = (encode (chordScale u v * (1+u*v)),
        encode (chordScale u v * (u*v-1)),
        encode (chordScale u v * (-(u+v)))) ∧
      (coreMatrix half alpha (decode data.abc.1) (decode data.abc.2.1)
        (decode data.abc.2.2)).det =
          (chordScale u v)^271 * (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det ∧
      ((coreMatrix half alpha (decode data.abc.1) (decode data.abc.2.1)
        (decode data.abc.2.2)).det ≠ 0 ↔
          (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det ≠ 0) := by
  refine ⟨exactData s z b0 b1 again, rawData_exact s z hsx hsy hzx hzy hsz b0 b1 again, ?_⟩
  have hc := rational_chord_normalization u v hu hv
  have habc : (exactData s z b0 b1 again).abc =
      (encode (chordScale u v * (1+u*v)),
       encode (chordScale u v * (u*v-1)),
       encode (chordScale u v * (-(u+v)))) := by
    simp only [exactData, hx0, hy0, hx1, hy1, hc.1, hc.2.1, hc.2.2]
  refine ⟨habc, ?_⟩
  rw [habc]
  simp only [R165QuarticExecution.decode_encode]
  trace_state
  constructor
  · exact @coreMatrix_det_chord_scale QM31Exact inferInstance inferInstance half alpha (1+u*v) (u*v-1) (-(u+v)) (chordScale u v)
  · exact @coreMatrix_det_ne_zero_iff_chord_scale QM31Exact inferInstance inferInstance half alpha (1+u*v) (u*v-1) (-(u+v)) (chordScale u v)
      (chordScale_ne_zero u v AspisV8R15.ExactTowerChord.two_ne_zero hu hv hne)

#print axioms selected_rawData_core
end
end AspisV8R19.R596SelectedChordCore
