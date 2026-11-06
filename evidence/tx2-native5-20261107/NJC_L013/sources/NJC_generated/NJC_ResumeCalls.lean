import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_ResumeCalls
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def digest {H : Type} (d : VTop_Stages.aspis_core.digest.Digest32 H) :
 AspisR1Stage2.aspis_core.digest.Digest32 H := ⟨d.coremarkerCopyInst,d.digest⟩

def cohort (reserved : Bool) {H : Type} (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :=
 verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (digest d) ck proof pub v hash

/-- Actual retained emitted resume body with its explicitly named reference
primitive dictionary. S1/D are left as the cohort body; the parent enters S2.
This installs the source occurrence, but DOES NOT assert the unclosed native
primitive/allocator/header dictionary equals this reference dictionary. -/
def reference (reserved : Bool) {H : Type} (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :=
 match v with
 | .S2 => NIL_StatePort.reply (NIL_FreshOps.resume reserved (digest d) ck proof pub .S2 hash)
 | _ => cohort reserved d ck proof pub v hash

theorem clause (reserved : Bool) {H : Type} (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 reference reserved d ck proof pub v hash=cohort reserved d ck proof pub v hash := by
 cases v with
 | S1 => rfl
 | D => rfl
 | S2 => exact NIY_ResumePort.source reserved (digest d) ck proof pub hash

def literal (base : VTop_Stages.Ops) (reserved : Bool) : VTop_Stages.Ops :=
 {NJC_ClosedCalls.literal base with op18:=@reference reserved}

def model (base : VTop_Stages.Ops) (reserved : Bool) : VTop_Stages.Ops :=
 {NJC_ClosedCalls.cohort base with op18:=@cohort reserved}

theorem installed (base : VTop_Stages.Ops) (reserved : Bool) :
 literal base reserved=model base reserved := by
 have h : @reference reserved=@cohort reserved := by
  funext H d ck proof pub v hash
  exact clause reserved d ck proof pub v hash
 unfold literal model
 rw [h,NJC_ClosedCalls.installed]

/-- Complete emitted parent reference transport, not a native positive root.
Its arbitrary base still has OPEN Merkle/query/flush/finish and allocator/ABI
producer association. The full statement is printed for the (aq)(2) audit. -/
theorem parent (base : VTop_Stages.Ops) (reserved : Bool) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (literal base reserved) d pub proof ck hash none=
 NHT_EmittedCommon.tx2_common (model base reserved) d pub proof ck hash none := by
 rw [installed]

#print axioms clause
#print axioms installed
#print axioms parent
#print parent
end NJC_ResumeCalls
