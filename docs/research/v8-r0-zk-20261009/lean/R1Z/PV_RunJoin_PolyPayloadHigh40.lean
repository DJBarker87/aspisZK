import R1Z.PV_RunJoin_PolyHigh40
import R1Z.PV_RunJoin_PolyLoop38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyPayloadHigh40
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38
variable [ExternalTypes]

/-- High halves remain zero through the entire ordered coefficient payload. -/
theorem high (p : Nat → Q) (start n k j : Nat) (hk : k<n)
    (lo : 16≤j) (hi : j<32) :
    (payload p start n)[32*k+j]?=some 0#u8 := by
  induction n generalizing start k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add,payload]
      rw [List.getElem?_append_left (by rw [PV_RunJoin_PolyCell38.length];exact hi)]
      exact PV_RunJoin_PolyHigh40.high _ j lo hi
    | succ k =>
      rw [payload,List.getElem?_append_right (by rw [PV_RunJoin_PolyCell38.length];omega),
        PV_RunJoin_PolyCell38.length]
      have ix : 32*(k+1)+j-32=32*k+j := by omega
      rw [ix]
      exact ih (start+1) k (by omega)
#print axioms high
end R1Z.PV_RunJoin_PolyPayloadHigh40
