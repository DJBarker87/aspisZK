import F3T_AcceptedReplacement
import LogA_Dependencies
set_option autoImplicit false
namespace AspisR1.F3T_InitFrame
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem public_bytes (a b : Bytes) (r s : State)
    (same : PublicInitFrame.frame a r=PublicInitFrame.frame b s) : a=b := by
  have lengths := congrArg List.length same
  rw [PublicInitFrame.frame_length,PublicInitFrame.frame_length] at lengths
  have size : a.length=b.length := by omega
  unfold PublicInitFrame.frame TrailingStateFrame.frame PublicInitFrame.pre at same
  simp only [List.append_assoc] at same
  rw [← size] at same
  have tail := List.append_cancel_left same
  have tail := List.append_cancel_left tail
  have tail := List.append_cancel_left tail
  have take := congrArg (List.take a.length) tail
  rw [List.take_left,size,List.take_left] at take
  exact take

#print axioms public_bytes
end AspisR1.F3T_InitFrame
