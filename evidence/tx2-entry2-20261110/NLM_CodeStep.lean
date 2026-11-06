import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace NLM_CodeStep
open Aeneas Aeneas.Std AspisR1 AspisR1.CheckpointBytes5Effect
/-- Hash projection of one scalar source operation. SDK/allocator physical
frames must be retained by its separate native cut, not inferred here. -/
def select {A B : Type} (r : Result A) (k : A → NGP_L181.Observation B) : NGP_L181.Observation B :=
 match r with
 | .ok a => k a
 | .fail err => ⟨.fail err,[]⟩
 | .div => ⟨.div,[]⟩

theorem cut {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (r : Result A) (k : A → Code B) (observed : A → NGP_L181.Observation B)
 (tail : ∀ a,r=.ok a → NHZ_DRIVER.Cuts hashv (k a) (observed a).result (observed a).attempted) :
 NHZ_DRIVER.Cuts hashv (.step r k) (select r observed).result (select r observed).attempted := by
 cases r with
 | fail err => exact .leaf (.stepFail _ _ err rfl)
 | div => exact .leaf (.stepDiv _ _ rfl)
 | ok a => exact .leaf (.stepOk _ _ _ rfl _ _ (NHZ_DRIVER.trace (tail a rfl)))
#print cut
#print axioms cut
end NLM_CodeStep
