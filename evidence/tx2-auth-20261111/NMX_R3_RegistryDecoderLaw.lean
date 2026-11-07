import NMX_R3_RegistryEffectLaws
import LIBB_ResultTotal
import LIBB_V1DecoderValues
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDecoderLaw
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def next {A E : Type} (k : A → RSL.Spec Output) (r : core.result.Result A E) : RSL.Spec Output :=
 match r with | .Ok a => k a | .Err _ => RSL.Spec.pure (.Err .InvalidAccountData)

/-- Totality comes from the CLOSED pure decoder at the exact reached bytes.
Every format error maps at this source occurrence to InvalidAccountData. -/
theorem fold {A B E : Type} (r : Result (core.result.Result A E))
 (total : LIBB_ResultTotal.Total r) (carrier : A → B)
 (k : A → RSL.Spec Output) (f : B → RSL.RS Unit)
 (hk : ∀ a, RSL.Spec.map (reply id) (k a) = f (carrier a)) :
 RSL.Spec.map (reply id) (RSL.Spec.bind (scalarSpec r) (next k)) =
 RSL.RS.bind (RSL.RS.ofOption
  (LIBB_V1DecoderValues.asOption carrier (LIBB_ResultTotal.value r total)) .invalidAccountData) f := by
 conv_lhs => rw [LIBB_ResultTotal.equation r total]
 simp only [scalarSpec,RSL.Spec.bind_pure]
 generalize LIBB_ResultTotal.value r total = out
 cases out with
 | Ok a =>
  change RSL.Spec.map (reply id) (k a) = RSL.RS.bind (RSL.RS.pure (carrier a)) f
  rw [RSL.RS.bind_pure]
  exact hk a
 | Err e =>
  change RSL.Spec.map (reply id) (RSL.Spec.pure (.Err .InvalidAccountData : Output)) =
   RSL.RS.bind (RSL.RS.throw .invalidAccountData) f
  rw [RSL.RS.bind_throw,map_pure]
  rfl
#print axioms fold
end NMX_R3_RegistryDecoderLaw
end
