import CuSavingsGammaPreparation
import CuSavingsGammaCaller

/-! Compose the complete source preparation comparison with retained-table
caller substitution. The sole changed-helper contract remains explicit:
old claim execution factors through the same power table and new claim.
Its source discharge and the tx1 wrapper admission are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsGammaTransfer
open Aeneas Aeneas.Std Result AspisR1CuGamma
open CuSavingsGammaTable CuSavingsGammaPreparation CuSavingsGammaCaller
variable [Boundaries]

def reference {H A : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (onError : Err → Result A) (context : Prepared → Result Table → Result A) : Result A := do
  let result ← gamma_old.Prepared.gamma_old_new D sem v hash
  match result with
  | .Err error => onError error
  | .Ok p => context p (weights.powers 29#usize p.gamma)

theorem callers_eq_of_claim_factor {H A : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (initial : Table)
    (onError : Err → Result A) (context : Prepared → Result Table → Result A)
    (claim_factor : ∀ gamma kappa,
      gamma_old.prepared_claim D sem v.y1 v.inactive gamma kappa =
        (do let g ← weights.powers 29#usize gamma
            gamma_new.prepared_claim D sem v.y1 v.inactive g kappa)) :
    reference D sem v hash onError context =
      retaining D sem v hash initial onError context := by
  calc
    reference D sem v hash onError context =
        recomputing D sem v hash initial onError context := by
      unfold reference recomputing
      rw [preparations_eq D sem v hash initial claim_factor]
      unfold erase
      cases gamma_new.Prepared.gamma_new_new D sem v hash initial with
      | fail e => rfl
      | div => rfl
      | ok pair => rcases pair with ⟨result,g⟩;rfl
    _ = retaining D sem v hash initial onError context :=
      CuSavingsGammaCaller.callers_eq D sem v hash initial onError context

#print axioms reference
#print axioms callers_eq_of_claim_factor
end AspisR1.CuSavingsGammaTransfer
