import NNG_FirstStep345
-- Reference fold only until actual emitted source interpretation is paired.
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

/-- Source-ordered observable fold. This is the revised source interpretation;
the emitted-body association and concrete CLOSED-library installation remain
separate obligations, not assumptions on345's input. -/
def bodyRun (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (child : TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
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

theorem body_packet (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (library : ValidatedPublic V C) (lengths : TX1_345.P1880Discharge V C) (allocation : Allocation)
 (child : TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_328.RowSpec_328 V P child) (s : Parent) (env : Env) :
 TX1_345.body V P C s.original s.proofAccount s.publicAccount s.checkpointAccount
  env (bodyRun V C allocation child s env) := by
 unfold TX1_345.body bodyRun
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
 intro st decoded
 let d : Decoded V C := ⟨⟨⟨s,ck⟩,pub⟩,st,decoded⟩
 apply stepValidate_valid V C d
 intro validated
 let v : Validated V C := ⟨d,validated⟩
 apply stepEncode_valid V C v
 intro candidate
 let c : Candidate V C := ⟨v,candidate⟩
 apply stepProofData_valid V C allocation c
 intro proof
 let p : ProofData V C := ⟨c,proof⟩
 apply stepProofGuard_valid V C p
 exact stepFirst_valid V P C library lengths child packet p env

def run (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (child : TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (a : TX1_345.Args) (env : Env) : Obs (Except ProgramError Bytes) :=
 if TX1_345.badRoute a then silent (.error .invalidInstructionData) else
 match a.accounts with
 | [p,pub,ck] => bodyRun V C allocation child ⟨a,p,pub,ck⟩ env
 | _ => stopped

/-- Full canonical reference fold over the observable source interpretation.
Not an actual-emitted candidate until the concrete library and source
interpretation have been connected; no parent own-input clause is added. -/
theorem reference_packet (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (library : ValidatedPublic V C) (lengths : TX1_345.P1880Discharge V C) (allocation : Allocation)
 (child : TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_328.RowSpec_328 V P child) :
 TX1_345.RowSpec_345 V P C (run V C allocation child) := by
 intro a env _
 have panic : (RS.lift (Spec.panic : Spec Bytes)) env (stopped : Obs (Except ProgramError Bytes)) :=
  Or.inr (Or.inl ⟨[],rfl,rfl⟩)
 unfold TX1_345.Ref run
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
      | nil => exact body_packet V P C library lengths allocation child packet ⟨a,p,pub,ck⟩ env
      | cons fourth rest => exact panic
#print axioms body_packet
#print axioms reference_packet
end AspisR1.NNG_Phases345
