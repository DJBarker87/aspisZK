import NEJ_ArrayFrame
import NED_WindowExtensionality
set_option autoImplicit false
noncomputable section
namespace NEL_CopyArrayLaw
open Aeneas Aeneas.Std Result

theorem list_inside {α : Type} (dst src : List α) (start k : Nat)
    (fits : start + src.length ≤ dst.length)
    (inside : start ≤ k ∧ k < start + src.length) :
    (dst.setSlice! start src)[k]? = src[k-start]? := by
  have hs : start ≤ dst.length := by omega
  have hroom : min src.length (dst.length-start) = src.length := Nat.min_eq_left (by omega)
  simp only [List.setSlice!, hroom, List.take_length]
  rw [List.append_assoc]
  have hlen : (dst.take start).length = start := by
    exact (List.length_take).trans (Nat.min_eq_left hs)
  rw [List.getElem?_append_right (by rw [hlen]; omega)]
  rw [List.getElem?_append_left (by rw [hlen]; omega)]
  rw [hlen]

theorem array_spec {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val) :
    (dst.setSlice! start src.val).val[k]? =
      if start ≤ k ∧ k < start + W.val then src.val[k-start]? else dst.val[k]? := by
  by_cases hi : start ≤ k ∧ k < start + W.val
  · rw [if_pos hi]
    change (dst.val.setSlice! start src.val)[k]? = _
    apply list_inside
    · simpa only [src.property,dst.property] using fits
    · simpa only [src.property] using hi
  · rw [if_neg hi]
    apply NEJ_ArrayFrame.array_frame
    · simpa only [src.property] using fits
    · simpa only [src.property] using (show k < start ∨ start + W.val ≤ k by omega)

/-- Exact KMX value-loop to emitted back-write association on one arbitrary
complete prestate. Both touched values and every external frame byte agree. -/
theorem loop_binding {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val) :
    KMX_CopyMeaning.loop (fun j => src.val[j-start]?) (fun j => dst.val[j]?) start W.val k =
      (dst.setSlice! start src.val).val[k]? := by
  rw [KMX_CopyMeaning.loop_spec, array_spec dst src start k fits]

#print axioms list_inside
#print axioms array_spec
#print axioms loop_binding
end NEL_CopyArrayLaw
