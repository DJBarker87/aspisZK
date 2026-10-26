import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Quantifiers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open F3T_ByteCarrier SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- Deployment means both projections come from ONE adversary. This is an
image/index definition, not a source-equality or cryptographic assumption. -/
def Deployed (P : ByteProver) (r : F3T_Runtime.Runtime) : Prop :=
  ∃ a : Adversary A, P = submission a ∧ r = runtime c hashv copy allocator id a

/-- Explicit quantifier correction. Universal shared-adversary statements are
exactly the old independent-binder form RESTRICTED to genuine deployed pairs.
No claim about every arbitrary pair, nor surjectivity onto them, is made. -/
theorem deployed_iff (R : ByteProver → F3T_Runtime.Runtime → Prop) :
    (∀ a : Adversary A, R (submission a) (runtime c hashv copy allocator id a)) ↔
    (∀ P r, Deployed c hashv copy allocator id P r → R P r) := by
  constructor
  · intro all P r ⟨a,hP,hr⟩
    subst P; subst r
    exact all a
  · intro all a
    exact all _ _ ⟨a,rfl,rfl⟩

/-- Old deployments can use every new conclusion without an independent
observer law once their actual construction identifies the shared pair. -/
theorem old_use (R : ByteProver → F3T_Runtime.Runtime → Prop)
    (new : ∀ a : Adversary A, R (submission a) (runtime c hashv copy allocator id a))
    (P : ByteProver) (r : F3T_Runtime.Runtime)
    (genuine : Deployed c hashv copy allocator id P r) : R P r :=
  (deployed_iff c hashv copy allocator id R).mp new P r genuine

#print axioms deployed_iff
#print axioms old_use
end AspisR1.SCE_Quantifiers
end
