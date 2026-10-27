import SCE_Quantifiers
import SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_DeploymentProjection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier
/-- The old stored-observation subclause is proved on the explicitly corrected
shared-adversary domain, even for rejected runs. It is not full L159. -/
theorem stored {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (P : ByteProver) (r : F3T_Runtime.Runtime)
    (genuine : SCE_Quantifiers.Deployed c hashv copy allocator id P r)
    (H : Bytes → State) (run : RunView) (observed : (eval H r).2 = some run) :
    run.2.1.stored = (eval H P).2.stored := by
  obtain ⟨a,rfl,rfl⟩ := genuine
  exact SCE_Projection.stored c hashv copy allocator id a H run observed
#print axioms stored
end AspisR1.SCE_DeploymentProjection
end
