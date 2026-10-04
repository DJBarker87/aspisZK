import AspisV8R19.R596SelectedChordCore
import AspisV8R19.R211CircleDomain

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R597SampledChordCore
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core AspisV8R15.ExactTowerBase
open R165QuarticExecution (Canonical decode)
open R164ProductExecution (encode)
open R203ChordDataExecution R574SparseGCorePolynomial R596SelectedChordCore
open AspisV8R17 DuplexFrames SourceDuplexStep
noncomputable section
local instance : NeZero (2 : QM31Exact) := ⟨AspisV8R15.ExactTowerChord.two_ne_zero⟩

theorem sampled_chord_core (H : Bytes → State) (s0 s1 : State)
    (p0 p1 : circle.SecureCirclePoint) (next0 next1 : transcript.Transcript)
    (h0 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s0) = .ok (.Ok p0,next0))
    (h1 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s1) = .ok (.Ok p1,next1))
    (hne : p0 ≠ p1) (half alpha b0 b1 again : QM31Exact) :
    ∃ u v : QM31Exact, ∃ data : ChordData,
      u.im ≠ 0 ∧ v.im ≠ 0 ∧ v ≠ u ∧
      rawData p0 p1 (encode b0) (encode b1) (encode again) = .ok (.Ok data) ∧
      data.abc = (encode (chordScale u v * (1+u*v)),
        encode (chordScale u v * (u*v-1)),encode (chordScale u v * (-(u+v)))) ∧
      (coreMatrix half alpha (decode data.abc.1) (decode data.abc.2.1)
        (decode data.abc.2.2)).det =
          (chordScale u v)^271 * (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det ∧
      ((coreMatrix half alpha (decode data.abc.1) (decode data.abc.2.1)
        (decode data.abc.2.2)).det ≠ 0 ↔
          (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det ≠ 0) := by
  obtain ⟨u,huim,hu,hp0⟩ := R211CircleDomain.successful_parameter H s0 p0 next0 h0
  obtain ⟨v,hvim,hv,hp1⟩ := R211CircleDomain.successful_parameter H s1 p1 next1 h1
  have hcan0 : Canonical p0.x ∧ Canonical p0.y := by
    rw [hp0]
    exact R166CircleExecution.point_canonical _
  have hcan1 : Canonical p1.x ∧ Canonical p1.y := by
    rw [hp1]
    exact R166CircleExecution.point_canonical _
  have huv : v ≠ u := by
    intro h
    apply hne
    rw [hp0,hp1,h]
  have hx0 : decode p0.x = rationalX u := by
    rw [hp0]
    simp only [R166CircleExecution.encodePoint, SamplerCirclePolicy.point,
      R165QuarticExecution.decode_encode]
    rfl
  have hy0 : decode p0.y = rationalY u := by
    rw [hp0]
    simp only [R166CircleExecution.encodePoint, SamplerCirclePolicy.point,
      R165QuarticExecution.decode_encode]
    rfl
  have hx1 : decode p1.x = rationalX v := by
    rw [hp1]
    simp only [R166CircleExecution.encodePoint, SamplerCirclePolicy.point,
      R165QuarticExecution.decode_encode]
    rfl
  have hy1 : decode p1.y = rationalY v := by
    rw [hp1]
    simp only [R166CircleExecution.encodePoint, SamplerCirclePolicy.point,
      R165QuarticExecution.decode_encode]
    rfl
  obtain ⟨data,hdata⟩ := selected_rawData_core p0 p1 hcan0.1 hcan0.2 hcan1.1 hcan1.2
    hne u v half alpha b0 b1 again hu hv huv hx0 hy0 hx1 hy1
  exact ⟨u,v,data,huim,hvim,huv,hdata⟩

#print axioms sampled_chord_core
end
end AspisV8R19.R597SampledChordCore
