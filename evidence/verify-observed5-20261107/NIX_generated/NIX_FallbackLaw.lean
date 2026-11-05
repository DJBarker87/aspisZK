import NIH_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_FallbackLaw
open Aeneas Aeneas.Std Result
open AspisR1CircleSampleWrapper
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open R0P.SemSource

def expected : r0_transcript.CircleRow → circle.SecureCirclePoint
 | .First=>fromFallbackPoint (AspisR1CircleFallback.fromR72Point
   (encodePoint (point circleFallbackParameter0)))
 | .Second=>fromFallbackPoint (AspisR1CircleFallback.fromR72Point
   (encodePoint (point circleFallbackParameter1)))

def index : r0_transcript.CircleRow → Usize | .First=>0#usize | .Second=>1#usize

theorem first : _root_.transcript.circle_fallback_point 0#usize=ok (expected .First) := by
 unfold _root_.transcript.circle_fallback_point
 rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_zero_output]
 rfl

theorem second : _root_.transcript.circle_fallback_point 1#usize=ok (expected .Second) := by
 unfold _root_.transcript.circle_fallback_point
 rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_one_output]
 rfl

/-- The native fallback packet covers every usize. These are precisely the
TWO deployed caller instances selected by CircleRow, not an unstated restriction. -/
theorem deployed (row : r0_transcript.CircleRow) :
 _root_.transcript.circle_fallback_point (index row)=ok (expected row) := by
 cases row
 · exact first
 · exact second

#print axioms first
#print axioms second
#print axioms deployed
end AspisR1.NIX_FallbackLaw
end
