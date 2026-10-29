import R1Z.PV_OWND_PaddedFold
set_option autoImplicit false
namespace R1Z.PV_OWND_PaddedValues
open PV_OWNC_Vector PV_OWN_View PV_OWN_Bytes PV_OWND_PaddedFold

theorem retained {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j i : Nat) (hi:i<b.length) :
 (append k b xs payload j).values i=b.values i := by
 induction xs generalizing b j with
 | nil => rfl
 | cons v vs ih =>
  rw [append,ih]
  · simp only [push,show i≠b.length by omega,ite_false]
  · change i<b.length+1
    omega

theorem suffix {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j i : Nat) (hi:i<xs.length) :
 (append k b xs payload j).values (b.length+i)=xs[i] := by
 induction xs generalizing b j i with
 | nil => simp only [List.length_nil] at hi;omega
 | cons v vs ih =>
  cases i with
  | zero =>
   rw [append]
   simp only [Nat.add_zero,List.getElem_cons_zero]
   rw [retained k (push k b v (payload j v)) vs payload (j+1) b.length
    (by change b.length<b.length+1;omega)]
   simp only [push,ite_true,List.getElem_cons_zero]
  | succ i =>
   have lt:i<vs.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
   rw [append]
   have h:=ih (push k b v (payload j v)) (j+1) i lt
   change (append k (push k b v (payload j v)) vs payload (j+1)).values (b.length+1+i)=vs[i] at h
   simpa only [Nat.add_assoc,Nat.add_comm 1 i,List.getElem_cons_succ] using h
#print axioms retained
#print axioms suffix
end R1Z.PV_OWND_PaddedValues
