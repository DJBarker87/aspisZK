import R1Z.PV_RunJoin_PolyCanonical40
import R1Z.PV_RunJoin_ArrayEntries41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyArrayCanonical41
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PolyCell38
variable [ExternalTypes]

/-- Every actual polynomial returned by the current interpolator has the
required encoder byte domain, without an oracle-meaning premise. -/
theorem encode (ops : ExternalFuns) (polynomial : Array Q 28#usize) :
    ∃ bytes, @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops)
      polynomial=.ok bytes ∧ bytes.length=896 ∧
      PV_RunJoin_HighDomain40.HighZero bytes.val := by
  let zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
  let p := PV_RunJoin_ArrayEntries41.entries polynomial zero
  obtain ⟨bytes,hb,hv,hl,hz⟩ := PV_RunJoin_PolyCanonical40.encode ops p
  rw [PV_RunJoin_ArrayEntries41.rebuild polynomial zero] at hb
  exact ⟨bytes,hb,hl,hz⟩
#print axioms encode
end R1Z.PV_RunJoin_PolyArrayCanonical41
