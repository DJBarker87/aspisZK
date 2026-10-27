import R1Z.PV_CBL_PaddingModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingRetention
open PV_CBL_PaddingModel
set_option autoImplicit false
theorem zero_position (buffer suffix : List U8) (pos : Nat) :
    (retained buffer pos suffix).2=0 := rfl
theorem first_buffer (buffer suffix : List U8) (pos : Nat) :
    (retained buffer pos suffix).1=first buffer pos suffix := rfl
theorem two_retains_delimited (buffer suffix : List U8) (pos : Nat) (h : 56≤pos) :
    (retained buffer pos suffix).1=delimited buffer pos := by
  simp [retained,first,show ¬pos<56 by omega]
#print axioms zero_position
#print axioms first_buffer
#print axioms two_retains_delimited
end R1Z.PV_CBL_PaddingRetention
