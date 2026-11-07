import NLJ_RowSpec094
set_option autoImplicit false
noncomputable section
namespace NMB_RowSpec094
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller AspisR1.NLJ_Packets
/-- Every external frame component, with no projection discarded. -/
def FrameEqual (after before : Frame094) : Prop :=
 after.proof=before.proof ∧ after.publicBytes=before.publicBytes ∧
 after.externalBytes=before.externalBytes ∧ after.externalMetadata=before.externalMetadata ∧
 after.authority=before.authority
theorem frame_iff (after before : Frame094) : after=before ↔ FrameEqual after before := by
 cases after
 cases before
 simp [FrameEqual]
/-- Original schema VALUE/FRAME projection, not the full ledger resource
obligation. This records full nominal
Result, ALL ordered attempted digests including abort attempts, SAME original
inputs and complete external frame. Physical native/carrier interpretation is
required of native and is NOT installed by this schema or its equivalence.
Allocator/lifetime/borrow/ABI packet completeness is also NOT proved here. -/
def Required (native : Native094) : Prop :=
 ∀ (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (before after : Frame094)
 (observed : NGP_L181.Observation (core.result.Result (alloc.vec.Vec U8) verifier.Error)),
 before.proof=proof → before.publicBytes=publicBytes →
 native base B std hashv D public1 publicBytes proof k before after observed →
 (observed.result,observed.attempted)=SdkC_Source.run hashv
   (NGQ_Normalize.normalize (GExp_FirstCode.code base B std hashv D public1 publicBytes proof k)) [] ∧
 FrameEqual after before
/-- Exact equivalence to the ORIGINAL unproved schema. This discharges no
native producer, caller clause, result or frame assumption. -/
theorem equivalent (native : Native094) : Required native ↔ RowSpec_094 native := by
 constructor
 · intro h base B std hashv D public1 publicBytes proof k before after observed hp hu entered
   have packet:=h base B std hashv D public1 publicBytes proof k before after observed hp hu entered
   exact ⟨packet.1,(frame_iff after before).mpr packet.2⟩
 · intro h base B std hashv D public1 publicBytes proof k before after observed hp hu entered
   have packet:=h base B std hashv D public1 publicBytes proof k before after observed hp hu entered
   exact ⟨packet.1,(frame_iff after before).mp packet.2⟩
#print Required
#print equivalent
#print axioms frame_iff
#print axioms equivalent
end NMB_RowSpec094
