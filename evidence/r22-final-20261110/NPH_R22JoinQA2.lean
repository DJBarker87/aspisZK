import NPH_R22JoinCW2
import NPH_R22JoinCW5
import CurrentClaimPowersInstance
import Tx2N_Powers

/-! NPH_ (R22, QA context "CurrentWideMulCanonical WideExact.mul callers").
The QA site AspisR1CurrentWideMul.field.wide_exact.WideExact.mul has one direct caller,
AspisR1PowersConcreteMul.sourceMul, whose only executing caller is
AspisR1LoopPowers.field.WideExact.mul in AspisR1LoopPowers.weights.early_powers_loop.body
(definition-level scan, NPH_POWERS_REFS in section 17b). early_powers has exactly two executing
callers: AspisR1CurrentPreparedClaim.ClaimPowers.powers (the concreteOps claim powers slot) and
AspisR1.Tx2N_Powers.powers (the tx2 stage op17 slot, NNH_Tx2LiteralSlots).
On a canonical input the WHOLE early_powers call is ok (AspisR1LoopPowers.early_powers_total_exact),
so every WideExact.mul call it executes returns ok.
- `claim_powers_ok`: the claim powers on a canonical kappa is ok. NPH_R22JoinCW5.guarded_claim_sites
  shows that every claim the deployed prepare executes has a canonical kappa, and the claim loop
  calls powers 7 on that kappa.
- `tx2_powers_ok`: Tx2N_Powers.powers 29 p.gamma is ok for the Prepared p returned by the tx2
  resume (gamma canonical from NID_ResumeFields.Domain, NPH_R22JoinCW2.entered_domain). tx2_common
  calls op17 only as op17 29 p.gamma on that p.
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinQA2
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete

theorem claim_powers_ok (kappa : PE) (hk : Canonical (toClaimE kappa)) :
    ∃ k, (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).powers
      7#usize (toClaimE kappa) = ok k := by
  obtain ⟨out, h, _⟩ := AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact 7#usize (toClaimE kappa) hk
  exact ⟨out, h⟩
#print axioms claim_powers_ok

end AspisR1.NPH_R22JoinQA2

namespace AspisR1.NPH_R22JoinQA2
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem tx2_powers_ok (reservation : NP6_StdModel.Reservation) {H : Type}
    (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash = ok (.Ok (p,a))) :
    ∃ g, Tx2N_Powers.powers 29#usize p.gamma = ok g := by
  have dom := (NPH_R22JoinCW2.entered_domain reservation d ck proof pub hash p a entered).1
  have hc : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers p.gamma) := by
    obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := dom.gamma
    first
      | exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩
      | exact ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩
  obtain ⟨out, h, _⟩ := Tx2N_Powers.total_exact 29#usize p.gamma hc
  exact ⟨out, h⟩
#print axioms tx2_powers_ok

end AspisR1.NPH_R22JoinQA2
