import ARP_Representation
import ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_Representation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- Exact carrier image, without inserting a bank-support promise or filter. -/
def Image (P : F3T_ByteCarrier.ByteProver) (r : F3T_Runtime.Runtime) : Prop :=
  ∃ a : Adversary A, P = submission a ∧ r = runtime c hashv copy allocator id a

theorem coverage_iff (R : F3T_ByteCarrier.ByteProver → F3T_Runtime.Runtime → Prop) :
    (∀ a : Adversary A, R (submission a) (runtime c hashv copy allocator id a)) ↔
    (∀ P r, Image c hashv copy allocator id P r → R P r) := by
  constructor
  · intro all P r ⟨a,hP,hr⟩
    subst P; subst r
    exact all a
  · intro all a
    exact all _ _ ⟨a,rfl,rfl⟩

/-- Therefore this image is strictly smaller than Rc9's independent carriers.
This does not refute representation of genuine deployed bank executions. -/
theorem missing_runtime (P : F3T_ByteCarrier.ByteProver) :
    ¬ Image c hashv copy allocator id P (.done none) := by
  rintro ⟨a,_,hr⟩
  exact ARP_Representation.not_independent_runtime c hashv copy allocator id a hr.symm

/-- Any original log/outcome cost or event functional is preserved pointwise.
This is not a new bit-cost implementation bound. -/
theorem original_law {V : Type} (cost : List (Bytes × State) × GExq_AccountExperiment.Outcome A → V)
    (a : Adversary A) (H : Bytes → State) :
    cost (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id))).2 =
      cost (eval H (account c hashv copy allocator id a)) := by
  rw [Hiq_RecordedJoint.source_view]

#print axioms coverage_iff
#print axioms missing_runtime
#print axioms original_law
end AspisR1.ARQ_Representation
end
