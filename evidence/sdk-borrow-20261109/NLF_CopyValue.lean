import NLF_ViewLaws
import KMX_CopyMeaning
set_option autoImplicit false
namespace NLF_CopyValue
open NLF_RefCell NLF_SdkModel
/-- Value composition over the exact KMX per-coordinate induction; no pointer,
allocation or native whole-buffer assertion is smuggled into this definition. -/
def copy (src dst : List UInt8) (start count : Nat) : List UInt8 :=
  List.ofFn (fun i : Fin dst.length =>
    KMX_CopyMeaning.loop (fun j => src[j]?.getD 0) (fun j => dst[j]?.getD 0) start count i.val)

theorem copy_length (src dst : List UInt8) (start count : Nat) :
    (copy src dst start count).length = dst.length := by simp [copy]

theorem copy_coordinate (src dst : List UInt8) (start count i : Nat) (hi : i<dst.length) :
    (copy src dst start count)[i]'(by simpa [copy_length] using hi) =
      if start ≤ i ∧ i<start+count then src[i]?.getD 0 else dst[i] := by
  simp [copy,KMX_CopyMeaning.loop_spec,hi]

theorem copy_frame (src dst : List UInt8) (start count i : Nat) (hi : i<dst.length)
    (outside : i < start ∨ start + count ≤ i) :
    (copy src dst start count)[i]'(by simpa [copy_length] using hi) = dst[i] := by
  rw [copy_coordinate]
  split_ifs with h
  · omega
  · rfl

theorem copy_whole (src dst : List UInt8) (same : src.length=dst.length) :
    copy src dst 0 dst.length = src := by
  apply List.ext_getElem
  · simpa [copy_length] using same.symm
  · intro i hi hj
    have hid : i<dst.length := by simpa [copy_length] using hi
    rw [copy_coordinate src dst 0 dst.length i hid]
    simp [hj,hid]

#print axioms copy_length
#print axioms copy_coordinate
#print axioms copy_frame
#print axioms copy_whole
end NLF_CopyValue
