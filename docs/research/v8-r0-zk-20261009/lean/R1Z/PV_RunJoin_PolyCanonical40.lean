import R1Z.PV_RunJoin_PolyPayloadHigh40
import R1Z.PV_RunJoin_HighDomain40
import R1Z.PV_RunJoin_PolyComplete38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyCanonical40
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38
variable [ExternalTypes]

theorem high (p : Nat → Q) (start n : Nat) :
    PV_RunJoin_HighDomain40.HighZero (payload p start n) := by
  intro k j bound lo hi
  rw [payload_length] at bound
  exact PV_RunJoin_PolyPayloadHigh40.high p start n k j (by omega) lo hi

/-- The actual encoder always supplies the compactor's high-half domain,
including arbitrary raw source inputs that are normalized by from_qm31. -/
theorem encode (ops : ExternalFuns) (p : Nat → Q) :
    ∃ bytes, @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 28#usize p)=.ok bytes ∧
      bytes.val=payload p 0 28 ∧ bytes.length=896 ∧
      PV_RunJoin_HighDomain40.HighZero bytes.val := by
  obtain ⟨bytes,hb,hv,hl⟩ := PV_RunJoin_PolyComplete38.encode ops p
  exact ⟨bytes,hb,hv,hl,by rw [hv];exact high p 0 28⟩
#print axioms high
#print axioms encode
end R1Z.PV_RunJoin_PolyCanonical40
