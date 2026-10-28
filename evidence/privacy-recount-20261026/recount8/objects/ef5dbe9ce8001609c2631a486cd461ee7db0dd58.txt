import R1Z.PV_RunJoin_CompactComplete39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactPayload39
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_CompactLoop39

/-- The source-ordered recurrence is exactly the independently indexed list
of low halves. No concrete long byte vector is normalized. -/
theorem indexed (logical : Slice U8) (start n : Nat) :
    payload logical start n =
      (List.ofFn (fun i : Fin n => (logical.val.drop (start+32*i.val)).take 16)).flatten := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [payload,List.ofFn_succ,List.flatten_cons]
    rw [ih]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 2
    simp only [Fin.val_succ]
    omega

theorem length (logical : Slice U8) (start n : Nat)
    (bound : start+32*n≤logical.length) :
    (payload logical start n).length=16*n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [payload,List.length_append,List.length_take,List.length_drop]
    have hb : start+32≤logical.val.length := by change start+32≤logical.length;omega
    rw [Nat.min_eq_left (by omega),ih (start+32) (by omega)]
    omega

#print axioms indexed
#print axioms length
end R1Z.PV_RunJoin_CompactPayload39
