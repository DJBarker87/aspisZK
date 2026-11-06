import NHV_NativeOps
import NHV_ReleaseOps
import NIY_ResumePort
import NFN_GeometryPart05
set_option autoImplicit false
noncomputable section
namespace NJC_ClosedCalls
open Aeneas Aeneas.Std Result AspisR1

/-- The actual extracted wide parser's complete Result, with the retained
nominal coordinate port. SAME input slice, no successful-output premise. -/
def inactive (bytes : Slice U8) := NHV_InactivePacket.emitted bytes

/-- The actual extracted geometry child's complete Result, including every
error/nonreturn arm. The result maps are the CLOSED row's own maps. -/
def geometry (queries : Array U32 22#usize) (start finish : Usize) :=
 Port3_QueryInstall.result
   (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
    NFN_NEW_GeometryRawInterface.answer
    (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))

theorem inactive_clause (bytes : Slice U8) :
 inactive bytes=NHV_InactivePacket.packet bytes :=
 (NHV_InactivePacket.source bytes).symm

theorem geometry_clause (queries : Array U32 22#usize) (start finish : Usize) :
 geometry queries start finish=
 Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted queries start finish :=
 NHV_NativeOps.geometry_result queries start finish

/-- Install the literal children at op2 and op11, not a freely chosen reply.
All other fields stay named and OPEN in base. This is not the final native root. -/
def literal (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
 {base with op2:=inactive,op11:=geometry}

def cohort (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
 {base with op2:=NHV_InactivePacket.packet,
  op11:=Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted}

/-- Each entered CLOSED child clause is discharged at all arguments. No
invocation relation or child Result equation is left as a hypothesis. -/
theorem installed (base : VTop_Stages.Ops) : literal base=cohort base := by
 have hi : inactive=NHV_InactivePacket.packet := funext inactive_clause
 have hg : geometry=Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted :=
  funext (fun queries=>funext (fun start=>funext (fun finish=>geometry_clause queries start finish)))
 unfold literal cohort
 rw [hi,hg]

/-- Full source-ordered parent transport for these two CLOSED occurrences.
The emitted body fixes their order and arguments. base still contains OPEN
resume/Merkle/pending/query/flush/finish producers; no native root is claimed. -/
theorem parent (base : VTop_Stages.Ops) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (public proof checkpoint : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (literal base) d public proof checkpoint hash none=
 NHT_EmittedCommon.tx2_common (cohort base) d public proof checkpoint hash none := by
 rw [installed]

/-- CLOSED getter law at the identical proof/index. No address-to-payload
inference is used, and no new getter native facet is introduced. -/
theorem opening_clause (proof : Slice U8) (index : Usize) :
 NEO_TailRef.opening proof index=Port4B_Opening.opening proof index :=
 NFN_NEO_TailReference.opening proof index

#print axioms inactive_clause
#print axioms geometry_clause
#print axioms installed
#print axioms parent
#print axioms opening_clause
#print parent
end NJC_ClosedCalls
