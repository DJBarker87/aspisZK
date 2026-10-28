import NCO_GlobalWord
import LPl_EcheckBytes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_WordDomain

theorem byte_window (payload : Slice U8) (i j lane : Nat) (hj : j < 8) (hl : lane < 4) :
    LPl.Echeck.byte ((((payload.val.drop (32*i)).take 32).drop (4*j)).take 4) lane =
      (NCO_Address.byte payload (32*i+4*j+lane)).val := by
  simp only [LPl.Echeck.byte,NCO_Address.byte,List.getElem?_take,hl,↓reduceIte,
    List.getElem?_drop,show 4*j+lane<32 by omega,↓reduceIte,Nat.add_assoc]

theorem value (payload : Slice U8) (i j : Nat) (hj : j < 8) :
    (NCO_GlobalWord.word payload i j).val =
      LPl_Kit_Bytes.le32 ((((payload.val.drop (32*i)).take 32).drop (4*j)).take 4) := by
  rw [← LPl.Echeck.word_eq_le32]
  unfold NCO_GlobalWord.word
  rw [NCO_WordNat.value]
  unfold LPl.Echeck.word
  simp only [byte_window payload i j 0 hj (by omega),
    byte_window payload i j 1 hj (by omega),byte_window payload i j 2 hj (by omega),
    byte_window payload i j 3 hj (by omega),Nat.add_zero]

#print axioms byte_window
#print axioms value
end NCO_WordDomain
