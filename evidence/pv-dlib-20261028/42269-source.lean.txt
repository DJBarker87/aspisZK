import R1Z.PV_CBL_PaddingModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingLength
open PV_CBL_PaddingModel
set_option autoImplicit false
theorem delimited_length (buffer : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) : (delimited buffer pos).length=64 := by
  simp only [delimited,List.length_append,List.length_take,List.length_singleton,List.length_replicate,hb]
  omega
theorem first_length (buffer suffix : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hs : suffix.length=8) :
    (first buffer pos suffix).length=64 := by
  unfold first
  split
  · simp only [List.length_append,List.length_take,delimited_length buffer pos hb hp,hs]
    decide
  · exact delimited_length buffer pos hb hp
theorem second_length (suffix : List U8) (pos : Nat) (hs : suffix.length=8)
    (block : List U8) (h : second pos suffix=some block) : block.length=64 := by
  unfold second at h
  split at h
  · contradiction
  · cases h
    simp [hs]
#print axioms delimited_length
#print axioms first_length
#print axioms second_length
end R1Z.PV_CBL_PaddingLength
