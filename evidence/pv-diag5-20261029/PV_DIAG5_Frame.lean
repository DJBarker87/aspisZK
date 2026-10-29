import PV_DIAG3_Capture
/-! Finite normally completed native callbacks. This discharges the bounds
of actual_start in Backtrace::Display, independently of the raw PCs. It does
not assert that the unwinder's raw frame sequence has a public joint law. -/
set_option autoImplicit false
namespace PV_DIAG5
open PV_DIAG3
def ValidStart (c : CaptureState) : Prop := ∀ k, c.actualStart = some k → k ≤ c.frames.length
def collect (ip : Nat) : List Frame → CaptureState → CaptureState
 | [],c => c
 | f::fs,c => collect ip fs (pushFrame ip c f)
def capturedFrames (ip : Nat) (fs : List Frame) : CaptureState := collect ip fs ⟨[],none⟩
def displayFrames (full : Bool) (c : CaptureState) : List Frame :=
 if full then c.frames else c.frames.drop (c.actualStart.getD 0)
-- STAGE
theorem empty_start_valid : ValidStart ⟨[],none⟩ := by
 intro k h; cases h
#print axioms empty_start_valid
-- STAGE
theorem push_start_valid (ip : Nat) (c : CaptureState) (f : Frame) (h : ValidStart c) :
 ValidStart (pushFrame ip c f) := by
 intro k hk
 simp only [pushFrame] at hk
 split at hk
 · cases hk; exact Nat.le_refl _
 · exact Nat.le_trans (h k hk) (by simp)
#print axioms push_start_valid
-- STAGE
theorem collect_start_valid (ip : Nat) (fs : List Frame) (c : CaptureState) (h : ValidStart c) :
 ValidStart (collect ip fs c) := by
 induction fs generalizing c with
 | nil => exact h
 | cons f fs ih => exact ih _ (push_start_valid ip c f h)
#print axioms collect_start_valid
-- STAGE
theorem captured_start_valid (ip : Nat) (fs : List Frame) :
 ValidStart (capturedFrames ip fs) := collect_start_valid ip fs _ empty_start_valid
#print axioms captured_start_valid
-- STAGE
theorem collect_frames (ip : Nat) (fs : List Frame) (c : CaptureState) :
 (collect ip fs c).frames = c.frames ++ fs := by
 induction fs generalizing c with
 | nil => simp [collect]
 | cons f fs ih => simp [collect,ih,pushFrame,List.append_assoc]
#print axioms collect_frames
-- STAGE
theorem captured_frames_exact (ip : Nat) (fs : List Frame) :
 (capturedFrames ip fs).frames = fs := by simp [capturedFrames,collect_frames]
#print axioms captured_frames_exact
-- STAGE
theorem start_getD_bound (c : CaptureState) (h : ValidStart c) :
 c.actualStart.getD 0 ≤ c.frames.length := by
 cases hs : c.actualStart with
 | none => simp [hs]
 | some k => exact h k hs
#print axioms start_getD_bound
-- STAGE
theorem actual_display_slice_valid (ip : Nat) (fs : List Frame) :
 (capturedFrames ip fs).actualStart.getD 0 ≤ fs.length := by
 have h := start_getD_bound _ (captured_start_valid ip fs)
 rw [captured_frames_exact] at h
 exact h
#print axioms actual_display_slice_valid
-- STAGE
theorem full_display_all (c : CaptureState) : displayFrames true c = c.frames := rfl
#print axioms full_display_all
-- STAGE
theorem short_display_suffix (c : CaptureState) :
 displayFrames false c = c.frames.drop (c.actualStart.getD 0) := rfl
#print axioms short_display_suffix
-- STAGE
theorem absent_start_all (fs : List Frame) : displayFrames false ⟨fs,none⟩ = fs := by
 simp [displayFrames]
#print axioms absent_start_all
-- STAGE
theorem at_end_no_frames (fs : List Frame) :
 displayFrames false ⟨fs,some fs.length⟩ = [] := by simp [displayFrames]
#print axioms at_end_no_frames
end PV_DIAG5
