import NJC_ResumeCalls
import NJC_QueryOccurrence
import NFW_PowersCohort
set_option autoImplicit false
noncomputable section
namespace NJC_OrderedCalls
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Complete deployed None marker clause consumed at both source positions.
This invokes the CLOSED release law; no Option<fn> Kani result is used. -/
theorem mark (base : VTop_Stages.Ops) (qbase : Port3_NativeQueryBody.Ops)
 (phase : VTop_Stages.verifier.Phase) :
 NHV_ReleaseOps.mark none phase=ok () :=
 NHV_ReleaseOps.release_mark base qbase 0 0 false phase

/-- The CLOSED native powers law, at the literal29 and SAME resumed gamma.
The canonical premise is an internal caller-domain obligation derived in
NJC_QueryOccurrence.closed, not an extra positive-root hypothesis. The exact
complete Result is Ok here; the theorem proves that no error arm is reached. -/
theorem powers (gamma : aspis_core.field.wide_exact.WideExact)
 (canonical : NFN_LPi_FieldValues.canonE (FIo_Install.toE gamma)) :
 ∃ out : Array NFN_LPi_FieldValues.NE 29#usize,
 FIo_Native.weights.powers 29#usize (FIo_Install.toE gamma)=ok out ∧
 NHT_PacketOps.powers 29#usize gamma=ok (FIp_DotsAdapter.fromArray out) ∧
 AspisR1ClaimPreparedBridge.powersPublic 29#usize
  (NFW_PowersCohort.toPublic (FIo_Install.toE gamma))=
 ok (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic out) ∧
 (∀ z∈out.val,NFN_LPi_FieldValues.canonE z) := by
 obtain ⟨out,native,model,values⟩ := NFW_PowersCohort.source 29#usize (FIo_Install.toE gamma) canonical
 exact ⟨out,native,NHT_PacketOps.powers_reply _ _ _ native,model,values⟩

def literal (base : VTop_Stages.Ops) (reserved : Bool) : VTop_Stages.Ops :=
 {NJC_ResumeCalls.literal base reserved with op13:=NHV_ReleaseOps.mark,op17:=NHT_PacketOps.powers}

def model (base : VTop_Stages.Ops) (reserved : Bool) : VTop_Stages.Ops :=
 {NJC_ResumeCalls.model base reserved with op13:=NHV_ReleaseOps.mark,op17:=NHT_PacketOps.powers}

theorem installed (base : VTop_Stages.Ops) (reserved : Bool) :
 literal base reserved=model base reserved := by
 unfold literal model
 rw [NJC_ResumeCalls.installed]

/-- Partial source-ordered root. Arbitrary base and the reference-only resume
primitive dictionary fail the (aq)(2) positive native-root inventory. -/
theorem parent (base : VTop_Stages.Ops) (reserved : Bool) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (literal base reserved) d pub proof ck hash none=
 NHT_EmittedCommon.tx2_common (model base reserved) d pub proof ck hash none := by
 rw [installed]

#print axioms mark
#print axioms powers
#print axioms installed
#print axioms parent
#print parent
end NJC_OrderedCalls
