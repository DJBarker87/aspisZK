import R1Z.PV_OWND_PushPrefix
set_option autoImplicit false
namespace R1Z.PV_OWND_PushSuffix
open PV_OWNC_Vector PV_OWNC_PushFold PV_OWN_View
/-- The suffix contains the full pushed values in source order. -/
theorem suffix {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (i : Nat) (hi:i<xs.length) : (append k b xs).values (b.length+i)=xs[i] := by
 induction xs generalizing b i with
 | nil => simp only [List.length_nil] at hi; omega
 | cons v vs ih =>
  cases i with
  | zero =>
   rw [append]
   rw [PV_OWND_PushPrefix.retained k (push k b v (k.encode v)) vs b.length (by change b.length<b.length+1;omega)]
   simp only [Nat.add_zero,push,ite_true,List.getElem_cons_zero]
  | succ i =>
   have lt:i<vs.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
   rw [append]
   have h:=ih (push k b v (k.encode v)) i lt
   change (append k (push k b v (k.encode v)) vs).values (b.length+1+i)=vs[i] at h
   simpa only [Nat.add_assoc,Nat.add_comm 1 i,List.getElem_cons_succ] using h
#print axioms suffix
end R1Z.PV_OWND_PushSuffix
