import R1Z.PV_RunJoin_ClaimImageList49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ClaimStreamCongruence49
theorem complete (f g : Nat → List UInt8) (h : ∀ l,l<29 → f l=g l)
    (start n : Nat) (bound : start+n≤29) :
    PV_RunJoin_ClaimImageList49.stream f start n=PV_RunJoin_ClaimImageList49.stream g start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [PV_RunJoin_ClaimImageList49.stream,PV_RunJoin_ClaimImageList49.stream,
      h start (by omega),ih (start+1) (by omega)]
#print axioms complete
end R1Z.PV_RunJoin_ClaimStreamCongruence49
