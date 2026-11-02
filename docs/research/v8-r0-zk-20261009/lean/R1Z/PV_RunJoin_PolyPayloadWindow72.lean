import R1Z.PV_RunJoin_PolyLoop38
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyPayloadWindow72
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38

theorem complete (p : Nat → Q) (start n i : Nat) (bound : i<n) :
    ((payload p start n).drop (32*i)).take 32=cell (p (start+i)) := by
  induction n generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero,List.drop_zero,Nat.add_zero,payload]
      rw [List.take_append,PV_RunJoin_PolyCell38.length]
      simp only [Nat.sub_self,List.take_zero,List.append_nil]
      exact List.take_of_length_le (by rw [PV_RunJoin_PolyCell38.length])
    | succ i =>
      rw [payload,List.drop_append]
      have drop : (cell (p start)).drop (32*(i+1))=[] :=
        List.drop_eq_nil_of_le (by rw [PV_RunJoin_PolyCell38.length];omega)
      rw [drop,List.nil_append,PV_RunJoin_PolyCell38.length]
      have off : 32*(i+1)-32=32*i := by omega
      rw [off,ih (start+1) i (by omega)]
      congr 2
      omega

#print axioms complete
end R1Z.PV_RunJoin_PolyPayloadWindow72
