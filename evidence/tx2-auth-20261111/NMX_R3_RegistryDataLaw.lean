import NMX_R3_RegistryCarrier
import NMX_R3_RegistryEffectLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDataLaw
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def next (k : Slice U8 → RSL.Spec Output)
 (r : core.result.Result (Slice U8) solana_program_error.ProgramError) : RSL.Spec Output :=
 match r with
 | .Ok q => k q
 | .Err e => RSL.Spec.pure (.Err e)

/-- Every getter outcome: the original Vec's full bytes, every complete error
payload, and the independent String-clone abort with its preceding prefix. -/
theorem fold (a : r1_pool_adapter.owned.OwnedAccount)
 (k : Slice U8 → RSL.Spec Output) (f : RSL.Bytes → RSL.RS Unit)
 (hk : ∀ q, RSL.Spec.map (reply id) (k q) = f (bytes q)) :
 RSL.Spec.map (reply id) (RSL.Spec.bind (dataSpec a) (next k)) =
 RSL.RS.bind (RSL.OwnedAccount.data (NMX_R3_RegistryCarrier.account a)) f := by
 cases hb : a.bytes with
 | Ok v =>
  simp only [dataSpec,hb,RSL.Spec.bind_pure,next]
  rw [hk]
  simp only [RSL.OwnedAccount.data,NMX_R3_RegistryCarrier.account,hb,reply,
   RSL.RS.ofCloned_ok,RSL.RS.bind_pure]
  rfl
 | Err e =>
  simp only [RSL.OwnedAccount.data,NMX_R3_RegistryCarrier.account,hb,reply]
  simp only [dataSpec,hb]
  change RSL.Spec.map (reply id)
   (RSL.Spec.bind (RSL.Spec.bind (RSL.Spec.allocIf (error e).cloneAllocates)
    (fun _ => RSL.Spec.pure (.Err e))) (next k)) = _
  change _ = RSL.RS.bind (RSL.RS.ofCloned (.error (error e))) f
  cases flag : (error e).cloneAllocates <;>
   simp only [RSL.RS.ofCloned,flag,Bool.false_eq_true,↓reduceIte,RSL.Spec.allocIf,
    RSL.Spec.map,NMX_R2_SpecAssociativity.bind,RSL.Spec.bind_pure,next,
    RSL.RS.bind,RSL.RS.lift,RSL.RS.throw,reply]
  <;> rfl

#print axioms fold
end NMX_R3_RegistryDataLaw
end
