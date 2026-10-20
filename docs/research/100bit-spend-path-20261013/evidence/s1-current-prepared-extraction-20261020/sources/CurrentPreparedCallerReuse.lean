import CurrentPreparedLegacyTransport
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PreparedScratchCallerReuse
open PreparedScratchReachability

/-- The retained caller model permits an arbitrary claim boundary. Choose it
as the current powers call followed by the current cached claim, preserving
all actual sampler operations. This does not assert an old Rust body equal. -/
def legacySampling (B : PreparedScratchModel.Boundaries) : PreparedModel.Boundaries :=
  { B.sampling with
    claim := fun D sem y inactive gamma kappa => do
      let scratch ← B.powers 29#usize gamma
      B.claim D sem y inactive scratch kappa }

def currentWithLegacySampling (B : PreparedScratchModel.Boundaries) :
    PreparedScratchModel.Boundaries :=
  { B with sampling := legacySampling B }

/-- Reusing the arbitrary retained claim boundary needs no independent
arithmetic-equivalence hypothesis for the sampler/caller trace. Actual powers
and cached-claim semantics remain explicit APIs in the current source model. -/
theorem current_success_reuses_caller_model {H : Type}
    (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratchIn scratch : Array Wide 29#usize)
    (h : PreparedScratchModel.prepare B D sem v hash scratchIn = ok (.Ok out, scratch)) :
    PreparedModel.prepare (legacySampling B) D sem v hash = ok (.Ok out) := by
  have agree : PreparedScratchTransport.ClaimsAgree (currentWithLegacySampling B) := by
    intro T DT st y inactive gamma kappa gs hpowers
    change B.powers 29#usize gamma = ok gs at hpowers
    change B.claim DT st y inactive gs kappa =
      (do let computed ← B.powers 29#usize gamma
          B.claim DT st y inactive computed kappa)
    rw [hpowers]
    rfl
  have hcurrent : PreparedScratchModel.prepare (currentWithLegacySampling B)
      D sem v hash scratchIn = ok (.Ok out, scratch) := by
    change PreparedScratchModel.prepare B D sem v hash scratchIn = ok (.Ok out, scratch)
    exact h
  exact PreparedScratchTransport.current_success_reuses_retained_prepare
    (currentWithLegacySampling B) agree D sem v hash out scratchIn scratch hcurrent

#print axioms current_success_reuses_caller_model
end AspisR1PublicPreparation.PreparedScratchCallerReuse
