import NMT_R2_345Distinct
import NMT_R2_345ReadonlyProof
import NMT_R2_345ReadonlyPublic
import NMT_R2_345Checkpoint
import NMT_R2_345CheckpointData
import NMT_R2_345Zero
import NMT_R2_345PublicData
import NMT_R2_345Decode
import NMT_R2_345Validate
import NMT_R2_345Encode
import NMT_R2_345ProofData
import NMT_R2_345ProofGuard
import NMT_R2_345First
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

/-- Source-ordered observable fold. This is the revised source interpretation;
the emitted-body association and concrete CLOSED-library installation remain
separate obligations, not assumptions on345's input. -/
def bodyRun (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (s : Parent) (env : Env) : Obs (Except ProgramError Bytes) :=
 stepDistinct s fun s =>
 stepReadonlyProof s fun s =>
 stepReadonlyPublic s fun s =>
 stepCheckpoint allocation s fun s =>
 stepCheckpointData allocation s fun s =>
 stepZero s fun s =>
 stepPublicData allocation s fun s =>
 stepDecode V C allocation s fun s =>
 stepValidate V C s fun s =>
 stepEncode V C s fun s =>
 stepProofData V C allocation s fun s =>
 stepProofGuard V C s fun s =>
 stepFirst V C child s env

theorem body_packet (V : VLib) (P : PreparedNew V) (C : NMT_R2.TX1_345.S1Lib V)
 (library : ValidatedPublic V C) (allocation : Allocation)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (packet : NMT_R2.TX1_328.RowSpec_328 V P child) (s : Parent) (env : Env) :
 NMT_R2.TX1_345.body V P C s.original s.proofAccount s.publicAccount s.checkpointAccount
  env (bodyRun V C allocation child s env) := by
 unfold NMT_R2.TX1_345.body bodyRun
 apply stepDistinct_valid
 apply stepReadonlyProof_valid
 apply stepReadonlyPublic_valid
 apply stepCheckpoint_valid
 apply stepCheckpointData_valid
 intro ck
 apply stepZero_valid ⟨s,ck⟩
 apply stepPublicData_valid allocation ⟨s,ck⟩
 intro pub
 apply stepDecode_valid V C allocation ⟨⟨s,ck⟩,pub⟩
 intro st
 apply stepValidate_valid V C ⟨⟨⟨s,ck⟩,pub⟩,st⟩
 intro validated
 apply stepEncode_valid V C ⟨⟨⟨⟨s,ck⟩,pub⟩,st⟩,validated⟩
 intro candidate
 apply stepProofData_valid V C allocation ⟨⟨⟨⟨⟨s,ck⟩,pub⟩,st⟩,validated⟩,candidate⟩
 intro proof
 apply stepProofGuard_valid V C ⟨⟨⟨⟨⟨⟨s,ck⟩,pub⟩,st⟩,validated⟩,candidate⟩,proof⟩
 exact stepFirst_valid V P C library child packet
  ⟨⟨⟨⟨⟨⟨s,ck⟩,pub⟩,st⟩,validated⟩,candidate⟩,proof⟩ env

def run (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (a : NMT_R2.TX1_345.Args) (env : Env) : Obs (Except ProgramError Bytes) :=
 if NMT_R2.TX1_345.badRoute a then silent (.error .invalidInstructionData) else
 match a.accounts with
 | [p,pub,ck] => bodyRun V C allocation child ⟨a,p,pub,ck⟩ env
 | _ => stopped

/-- Full canonical reference fold over the observable source interpretation.
Not an actual-emitted candidate until the concrete library and source
interpretation have been connected; no parent own-input clause is added. -/
theorem source_packet (V : VLib) (P : PreparedNew V) (C : NMT_R2.TX1_345.S1Lib V)
 (library : ValidatedPublic V C) (allocation : Allocation)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (packet : NMT_R2.TX1_328.RowSpec_328 V P child) :
 NMT_R2.TX1_345.RowSpec_345 V P C (run V C allocation child) := by
 intro a env _
 have panic : (RS.lift (Spec.panic : Spec Bytes)) env (stopped : Obs (Except ProgramError Bytes)) :=
  Or.inr (Or.inl ⟨[],rfl,rfl⟩)
 unfold NMT_R2.TX1_345.Ref run
 split
 · rfl
 · cases h : a.accounts with
   | nil => exact panic
   | cons p rest =>
    cases rest with
    | nil => exact panic
    | cons pub rest =>
     cases rest with
     | nil => exact panic
     | cons ck rest =>
      cases rest with
      | nil => exact body_packet V P C library allocation child packet ⟨a,p,pub,ck⟩ env
      | cons fourth rest => exact panic
#print axioms body_packet
#print axioms source_packet
end NMT_R2_345
