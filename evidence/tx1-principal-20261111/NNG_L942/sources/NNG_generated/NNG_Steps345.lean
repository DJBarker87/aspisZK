import NNG_Frames345
-- Canonical revision4 retarget of named NMT_R2 source observations.

-- Source: NMT_R2_345Distinct.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepDistinct (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount])) (fun _ => next s)

theorem stepDistinct_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount])) suffix env (stepDistinct s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepDistinct_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345ReadonlyProof.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepReadonlyProof (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (readonlyBuffer s.proofAccount)) (fun _ => next s)

theorem stepReadonlyProof_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (readonlyBuffer s.proofAccount)) suffix env (stepReadonlyProof s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepReadonlyProof_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345ReadonlyPublic.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepReadonlyPublic (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (readonlyBuffer s.publicAccount)) (fun _ => next s)

theorem stepReadonlyPublic_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (readonlyBuffer s.publicAccount)) suffix env (stepReadonlyPublic s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepReadonlyPublic_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345Checkpoint.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def checkpointObservation (keep : Bool) (a : OwnedAccount) (program : B32) (writable : Bool) :
 Obs (Except ProgramError Unit) :=
 if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
  silent (.error .invalidAccountData)
 else tryObs (cloned keep a.length) fun n => check (n != CHECKPOINT_BYTES) .invalidAccountData

theorem checkpointObservation_valid (keep : Bool) (a : OwnedAccount) (program : B32)
 (writable : Bool) (env : Env) :
 RSL.verifierCheckpoint a program writable env (checkpointObservation keep a program writable) := by
 unfold RSL.verifierCheckpoint checkpointObservation
 split
 · rfl
 · exact try_valid _ _ _ _ env (cloned_valid keep a.length env)
    (fun n => check_valid _ _ env)

def stepCheckpoint (allocation : Allocation) (s : Parent)
 (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (checkpointObservation (allocation 0) s.checkpointAccount s.original.program_id true) (fun _ => next s)

theorem stepCheckpoint_valid (allocation : Allocation) (s : Parent)
 (next : Parent → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : suffix env (next s)) :
 RS.seq (RSL.verifierCheckpoint s.checkpointAccount s.original.program_id true) suffix
  env (stepCheckpoint allocation s next) := by
 apply try_valid _ _ _ _ env (checkpointObservation_valid _ _ _ _ env)
 intro _
 exact later
#print axioms checkpointObservation_valid
#print axioms stepCheckpoint_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345CheckpointData.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepCheckpointData (allocation : Allocation) (s : Parent) (next : CheckpointData → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation 1) s.checkpointAccount.bytes) (fun bytes => next ⟨s,bytes⟩)

theorem stepCheckpointData_valid (allocation : Allocation) (s : Parent)
 (next : CheckpointData → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (RSL.OwnedAccount.data s.checkpointAccount) suffix env (stepCheckpointData allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms stepCheckpointData_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345Zero.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepZero (s : CheckpointData) (next : CheckpointData → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (requireZero s.checkpointData)) (fun _ => next s)

theorem stepZero_valid (s : CheckpointData) (next : CheckpointData → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (requireZero s.checkpointData)) suffix env (stepZero s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepZero_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345PublicData.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepPublicData (allocation : Allocation) (s : CheckpointData) (next : PublicData → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation 2) s.publicAccount.bytes) (fun bytes => next ⟨s,bytes⟩)

theorem stepPublicData_valid (allocation : Allocation) (s : CheckpointData)
 (next : PublicData → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (RSL.OwnedAccount.data s.publicAccount) suffix env (stepPublicData allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms stepPublicData_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345Validate.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepValidate (V : VLib) (C : TX1_345.S1Lib V) (s : Decoded V C)
 (next : Validated V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 if h : C.validateStatement s.statement = true then next ⟨s,h⟩
 else silent (.error .invalidAccountData)

theorem stepValidate_valid (V : VLib) (C : TX1_345.S1Lib V) (s : Decoded V C)
 (next : Validated V C → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : ∀ h : C.validateStatement s.statement = true, suffix env (next ⟨s,h⟩)) :
 RS.seq (RS.check (!C.validateStatement s.statement) .invalidAccountData) suffix env
  (stepValidate V C s next) := by
 cases hv : C.validateStatement s.statement with
 | false => simp only [hv,stepValidate,Bool.false_eq_true,not_false_eq_true,dif_neg,
      Bool.not_false,RS.check,if_true,RS.seq_throw]; rfl
 | true =>
  simp only [hv,stepValidate,dif_pos,Bool.not_true,RS.check,Bool.false_eq_true,if_false,RS.seq_pure]
  exact later hv
#print axioms stepValidate_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345Encode.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepEncode (V : VLib) (C : TX1_345.S1Lib V) (s : Validated V C)
 (next : Candidate V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 match C.encodeCandidate s.statement with
 | none => silent (.error .invalidAccountData)
 | some bytes => next ⟨s,bytes⟩

theorem stepEncode_valid (V : VLib) (C : TX1_345.S1Lib V) (s : Validated V C)
 (next : Candidate V C → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (RS.ofOption (C.encodeCandidate s.statement) .invalidAccountData) suffix env
  (stepEncode V C s next) := by
 unfold stepEncode
 cases he : C.encodeCandidate s.statement with
 | none => simp only [RS.ofOption,RS.bind_throw]; rfl
 | some bytes => simp only [RS.ofOption,RS.bind_pure]; exact later bytes
#print axioms stepEncode_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345ProofData.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepProofData (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : Candidate V C) (next : ProofData V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation 5) s.proofAccount.bytes) (fun bytes => next ⟨s,bytes⟩)

theorem stepProofData_valid (V : VLib) (C : TX1_345.S1Lib V) (allocation : Allocation)
 (s : Candidate V C) (next : ProofData V C → Obs (Except ProgramError Bytes))
 (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (RSL.OwnedAccount.data s.proofAccount) suffix env (stepProofData V C allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms stepProofData_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345ProofGuard.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def proofBad (V : VLib) (C : TX1_345.S1Lib V) (s : ProofData V C) : Bool :=
 s.proofData.length != PROOF_ACCOUNT_BYTES ||
 s.proofData.take AFTERSTATE_BYTES != s.candidate ||
 s.proofData.getD (AFTERSTATE_BYTES + 8) 0 != TX1_345.S2_TAG

def stepProofGuard (V : VLib) (C : TX1_345.S1Lib V) (s : ProofData V C)
 (next : ProofData V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (check (proofBad V C s) .invalidAccountData) (fun _ => next s)

theorem stepProofGuard_valid (V : VLib) (C : TX1_345.S1Lib V) (s : ProofData V C)
 (next : ProofData V C → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : suffix env (next s)) :
 RS.seq (RS.check (proofBad V C s) .invalidAccountData) suffix env
  (stepProofGuard V C s next) := by
 exact try_valid _ _ _ _ env (check_valid _ _ env) (fun _ => later)
#print axioms stepProofGuard_valid
end AspisR1.NNG_Phases345

-- Source: NMT_R2_345Return.lean
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL NNG_Obs345 NNG_Pure345

def stepReturn (length : Nat) (bytes : Bytes) : Obs (Except ProgramError Bytes) :=
 silent (if bytes.length != length then .error .invalidAccountData else .ok bytes)

theorem stepReturn_valid (length : Nat) (bytes : Bytes) (env : Env) :
 RS.seq (RS.check (bytes.length != length) .invalidAccountData) (RS.pure bytes)
  env (stepReturn length bytes) := by
 unfold stepReturn
 cases h : bytes.length != length <;>
  simp only [h,RS.check,Bool.false_eq_true,if_false,if_true,RS.seq_pure,RS.seq_throw] <;> rfl
#print axioms stepReturn_valid
end AspisR1.NNG_Phases345
