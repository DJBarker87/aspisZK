import NMX_R3_RegistryEffectLaws
import NND_ScalarLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPdaLaw
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def next (k : solana_pubkey.Pubkey → RSL.Spec Output)
 (r : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) : RSL.Spec Output :=
 match r with
 | .Ok q => k q
 | .Err _ => RSL.Spec.pure (.Err .InvalidAccountData)

theorem canonical_bind (seeds : List RSL.Bytes) (p : RSL.B32)
 (k : RSL.B32 → RSL.RS Unit) :
 RSL.RS.bind (RSL.pdaOrErr seeds p) k =
 RSL.Spec.bind (RSL.pdaCall seeds p)
  (fun r => match r with | some q => k q | none => RSL.RS.throw .invalidAccountData) := by
 unfold RSL.pdaOrErr RSL.RS.bind RSL.RS.lift RSL.Spec.map
 simp only [NMX_R2_SpecAssociativity.bind,RSL.Spec.bind_pure]
 apply congrArg (RSL.Spec.bind (RSL.pdaCall seeds p))
 funext r
 cases r <;> simp only [RSL.RS.ofOption,RSL.RS.pure,RSL.RS.throw,RSL.Spec.bind_pure]

/-- Full observation equality for a syscall occurrence, with the same seeds,
program, quantified reply and continuation, including the error reply. -/
theorem fold (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
 (k : solana_pubkey.Pubkey → RSL.Spec Output) (f : RSL.B32 → RSL.RS Unit)
 (hk : ∀ q, RSL.Spec.map (reply id) (k q) = f (key q)) :
 RSL.Spec.map (reply id) (RSL.Spec.bind (pdaSpec s p) (next k)) =
 RSL.RS.bind (RSL.pdaOrErr (s.val.map bytes) (key p)) f := by
 rw [canonical_bind]
 unfold pdaSpec RSL.Spec.map
 simp only [NMX_R2_SpecAssociativity.bind,RSL.Spec.bind_pure]
 apply congrArg (RSL.Spec.bind (RSL.pdaCall (s.val.map bytes) (key p)))
 funext r
 cases r with
 | none => simp only [next,RSL.Spec.bind_pure]; rfl
 | some q =>
  change RSL.Spec.map (reply id) (k (unkey q)) = f q
  rw [hk,NND_Carrier.key_forth]

#print axioms canonical_bind
#print axioms fold
end NMX_R3_RegistryPdaLaw
end
