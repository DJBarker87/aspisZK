import R1Z.PV_CBL_PadListFacts
import R1Z.PV_CBL_PaddingLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadModelBytes
set_option autoImplicit false
theorem delimited_byte (buffer : List U8) (pos j : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hj : j<64) :
    (PV_CBL_PaddingModel.delimited buffer pos)[j]! =
      if j < pos then buffer[j]! else if j=pos then 128#u8 else 0#u8 := by
  unfold PV_CBL_PaddingModel.delimited
  rw [List.append_assoc]
  have ht : (buffer.take pos).length=pos := by simp [hb,Nat.min_eq_left (by omega : pos≤64)]
  by_cases hlt : j < pos
  · rw [if_pos hlt]
    simp only [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simpa [ht] using hlt)]
    simp [List.getElem?_take,show j<pos by exact hlt]
  · rw [if_neg hlt]
    simp only [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega : (buffer.take pos).length≤j)]
    rw [ht]
    by_cases he : j=pos
    · subst j; simp
    · have hsub : 0<j-pos := by omega
      simp [List.getElem?_cons,show j-pos≠0 by omega,
        List.getElem?_replicate,show j-pos-1<63-pos by omega,he]
#print axioms delimited_byte
end R1Z.PV_CBL_PadModelBytes
