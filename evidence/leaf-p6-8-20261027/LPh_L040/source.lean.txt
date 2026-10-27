import LPa_Expand
import LPa_StageLaws
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace LPa.Expand

theorem loop_length (bs : List U8) (n : Nat) : (loop bs n).length = n :=
  LPa.build_length _ _

theorem low_half (bs : List U8) (i : Nat) (h : i%32 < 16) :
    byte bs i = bs[i/32*16+i%32]?.getD 0#u8 := by
  exact if_pos h

theorem high_half (bs : List U8) (i : Nat) (h : ¬ i%32 < 16) :
    byte bs i = 0#u8 := by
  exact if_neg h

-- The byte bound is the actual frozen y1 target size, not a new input premise.
theorem y1_loop_fold (bs : List U8) :
    loop bs (29*32) = (List.range (29*32)).foldl
      (fun xs i => xs ++ [byte bs i]) [] := loop_eq_fold _ _

#print axioms loop_length
#print axioms low_half
#print axioms high_half
#print axioms y1_loop_fold
end LPa.Expand
