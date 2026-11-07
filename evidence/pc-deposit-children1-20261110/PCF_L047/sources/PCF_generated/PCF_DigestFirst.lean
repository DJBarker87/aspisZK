import PCF_ChildLaws
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_DigestFirst
open AspisR1.S2K

def words (a b c d e f g h : U32) : Array U32 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]

/-- Later encoder windows cannot change a byte before their start. -/
theorem before (xs : List U32) (k : Nat) (out : Array U8 32#usize) (j : Nat)
    (prefix : j < 4*k) : (DigestBytes.fold xs k out)[j]! = out[j]! := by
  induction xs generalizing k out with
  | nil => rfl
  | cons x xs ih =>
    simp only [DigestBytes.fold]
    rw [ih (k+1) _ (by omega)]
    exact Array.setSlice!_getElem!_prefix _ _ _ _ prefix

theorem first_words (a b c d e f g h : U32) :
    NFY_NBN_OutputLane.first (words a b c d e f g h) =
      (core.num.U32.to_le_bytes a).val[0]! := by
  unfold NFY_NBN_OutputLane.first DigestBytes.bytes words
  change (DigestBytes.fold [b,c,d,e,f,g,h] 1
    ((Array.repeat 32#usize 0#u8).setSlice! 0 (core.num.U32.to_le_bytes a).val))[0]! = _
  rw [before _ 1 _ 0 (by decide)]
  exact Array.setSlice!_getElem!_middle _ _ 0 0 (by
    have hn := (core.num.U32.to_le_bytes a).property
    simp only [Array.length,Array.repeat] at *
    scalar_tac)

#print axioms before
#print axioms first_words
end PCF_DigestFirst
