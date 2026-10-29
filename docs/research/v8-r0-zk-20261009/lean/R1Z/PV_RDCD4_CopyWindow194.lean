import R1Z.PV_RDCD4_Copy194
set_option autoImplicit false
namespace R1Z.PV_RDCD4_CopyWindow194
open Aeneas Aeneas.Std Result

def splice {T : Type} (dst : List T) (base : Nat) (src : List T) : List T :=
  dst.take base ++ src ++ dst.drop (base+src.length)

def source {T : Type} (dst : List T) (base : Nat) (src : List T) : Result (List T) :=
  if base ≤ dst.length then
    if src.length ≤ dst.length-base then do
      let copied ← PV_RDCD4_Copy194.wrapper ((dst.drop base).take src.length) src
      ok (dst.take base ++ copied ++ dst.drop (base+src.length))
    else fail .arrayOutOfBounds
  else fail .arrayOutOfBounds

theorem binding {T : Type} (dst : List T) (base : Nat) (src : List T)
    (h : base+src.length ≤ dst.length) : source dst base src=ok (splice dst base src) := by
  have hl : ((dst.drop base).take src.length).length=src.length := by
    simp only [List.length_take,List.length_drop]
    exact Nat.min_eq_left (by omega)
  rw [source,if_pos (show base ≤ dst.length from by omega),
    if_pos (show src.length ≤ dst.length-base from by omega),
    PV_RDCD4_Copy194.success _ src hl,bind_tc_ok]

theorem length {T : Type} (dst : List T) (base : Nat) (src : List T)
    (h : base+src.length ≤ dst.length) : (splice dst base src).length=dst.length := by
  simp only [splice,List.length_append,List.length_take,List.length_drop]
  omega

theorem empty {T : Type} (dst : List T) (base : Nat) : splice dst base []=dst := by
  simp only [splice,List.length_nil,Nat.add_zero,List.nil_append,List.take_append_drop]

theorem short_position (pos n : Nat) (hp : pos < 64) (hn : n < 64-pos) :
    pos+n < 64 ∧ pos+n < 256 := by omega

#print axioms binding
#print axioms length
#print axioms empty
#print axioms short_position
end R1Z.PV_RDCD4_CopyWindow194
