import NND_PdaSeeds
import NND_FormatControl
set_option autoImplicit false
noncomputable section
namespace NND_PdaTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

/-- Exact parts order and program key are exposed to the SAME Env call; the
reply is converted without changing its bytes. This local value lemma does
not assert totality of an independent runtime syscall. -/
theorem value {B X : Type} (env : RSL.Env) (parts : Slice (Slice U8))
 (program : solana_pubkey.Pubkey) (k : solana_pubkey.Pubkey → NND_ProgramControl.P B)
 (g : B → X) (F : RSL.B32 → Except RSL.ProgramError X)
 (hk : ∀ p, outer (reply g) (k p) = ok (F (key p))) :
 outer (reply g) (NND_FormatControl.thenCall (NND_RegistryOps.pda env parts program) k) =
 ok (ebind (option (env.pda (parts.val.map bytes) (key program)) .invalidAccountData) F) := by
 unfold NND_RegistryOps.pda
 cases h : env.pda (parts.val.map bytes) (key program) with
 | none => rfl
 | some p =>
   change outer (reply g) (k (unkey p)) = ok (F p)
   rw [hk,key_forth]

#print axioms value
end NND_PdaTransport
end
