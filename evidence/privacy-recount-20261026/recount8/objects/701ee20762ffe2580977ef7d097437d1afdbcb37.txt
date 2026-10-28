import R1Z.PV_RunJoin_HighDomain40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_HighAppend41
open Aeneas Aeneas.Std PV_RunJoin_HighDomain40

theorem append (xs ys : List U8) (n : Nat) (length : xs.length=32*n)
    (left : HighZero xs) (right : HighZero ys) : HighZero (xs ++ ys) := by
  intro k j bound lo hi
  rw [List.length_append,length] at bound
  by_cases before : k<n
  · rw [List.getElem?_append_left (by rw [length];omega)]
    exact left k j (by omega) lo hi
  · rw [List.getElem?_append_right (by rw [length];omega),length]
    have offset : 32*k+j-32*n=32*(k-n)+j := by omega
    rw [offset]
    exact right (k-n) j (by omega) lo hi
#print axioms append
end R1Z.PV_RunJoin_HighAppend41
