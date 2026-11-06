import NLF_StateLaws
import NLF_CopyValue
set_option autoImplicit false
namespace NLF_ExclusiveBracket
open NLF_RefCell NLF_SdkModel

def copyDrop (s : State) (a t : Nat) (src : List UInt8) : Except Error State :=
  let i := (s.accounts a).data
  let held := put s i {s.cells i with writer:=some t}
  let value := {(s.cells i).payload with bytes:=NLF_CopyValue.copy src (s.cells i).payload.bytes 0 src.length}
  release (NLF_ViewLaws.write held ⟨i,t,.exclusive⟩ value) ⟨i,t,.exclusive⟩

theorem copy_drop (s : State) (a t : Nat) (src : List UInt8)
    (free : (s.cells (s.accounts a).data).writer=none)
    (same : src.length=(s.cells (s.accounts a).data).payload.bytes.length) :
    copyDrop s a t src = .ok (put s (s.accounts a).data
      {s.cells (s.accounts a).data with payload:={(s.cells (s.accounts a).data).payload with bytes:=src}}) := by
  unfold copyDrop
  rw [NLF_StateLaws.write_release s _ t _ free]
  rw [same,NLF_CopyValue.copy_whole src _ same]

/-- This proves admission of the actual wrapper BEFORE the copied/drop state
is used. No native returned guard or successful child result is assumed. -/
theorem exclusive_admission (s : State) (a t : Nat)
    (free : (s.cells (s.accounts a).data).writer=none)
    (empty : (s.cells (s.accounts a).data).readers=[]) :
    try_borrow_mut_data s a t =
      (put s (s.accounts a).data {s.cells (s.accounts a).data with writer:=some t},
       .ok ⟨(s.accounts a).data,t,.exclusive⟩) := exclusive_result s _ t free empty

#print axioms copy_drop
#print axioms exclusive_admission
end NLF_ExclusiveBracket
