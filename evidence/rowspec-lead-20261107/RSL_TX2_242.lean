/-
TX2:242  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8
Frozen signature (r1_pool_adapter_owned.rs:338):
  fn validate_asq8(verifier_program: &Pubkey, accounts: &[OwnedAccount],
      instruction_data: &[u8], current_slot: Result<u64, ProgramError>)
      -> Result<ValidatedAsqa, ProgramError>
Route: emitted body under (bm).
Children: OPEN TX2:233 (RowSpec_233 reference at SAME arguments); CLOSED
decode_pool_v1_pair_forest_terminal_request_v1 (TX2:163),
PoolV1PairForestTerminalPaymentV1::nullifier (TX2:158),
pool_v1_pair_forest_output_lane_v1 (TX2:156), pool_program_id (TX2:220),
OwnedAccount::data (TX2:229), scan_proof_buffer (TX2:226),
reconstruct_asq8_statement (TX2:224).
Own-input domain ((bf)(2)): none.
Effects: those of TX2:233 (PDA events) and of the CLOSED scan/reconstruct laws
(allocations), in source order.  The four Box owners returned by TX2:233 are
passed by reference to reconstruct and then dropped; the drop writes no account
or return data and is outside the obligation ((bl)(3)), so the spec carries the
owners in full through `authenticated` up to that call and no cleanup event.
Argument evaluation order at line 358-364: `current_slot?` is evaluated after
the request/lane checks and before TX2:233 is entered.
-/
import RSL_TX2_233
set_option autoImplicit false

namespace RSL.TX2_242

structure Args where
  verifier_program : B32
  accounts : List OwnedAccount
  instruction_data : Bytes
  current_slot : Except ProgramError UInt64

/-- `ValidatedAsqa` (r1_pool_adapter.rs:165-168). -/
structure Validated (L : PoolLib) where
  statement : L.Statement
  proof_length : Nat

def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS (Validated L) :=
  RS.seq (RS.check (a.instruction_data.length != REQUEST_BYTES) .invalidInstructionData) <|
  RS.bind (RS.ofOption (L.decodeRequest a.instruction_data) .invalidInstructionData) fun q =>
  RS.seq (RS.check (decide (L.reqProfile q ≠ PROFILE_BINDING)
                    || decide (L.reqRelease q ≠ RELEASE_BINDING)
                    || decide (L.reqPoolProgram q ≠ D.pool)) .invalidInstructionData) <|
  let pool := L.reqPoolProgram q
  RS.bind (RS.ofOption (L.outputLane (L.reqNullifier q)) .invalidInstructionData) fun lane =>
  RS.bind (RS.ofExcept a.current_slot) fun slot =>
  RS.bind (Spec.call TX2_233.Domain (TX2_233.Ref L D)
            ⟨a.verifier_program, a.accounts, pool, lane, slot⟩) fun auth =>
  RS.bind (RS.ofOption a.accounts.head? .notEnoughAccountKeys) fun proofAccount =>
  RS.bind (RS.ofExcept proofAccount.data) fun pdata =>
  RS.bind (L.scanProof pdata) fun scanned =>
  RS.bind (L.reconstruct q auth scanned.1) fun statement =>
  RS.pure { statement := statement, proof_length := scanned.2 }

/-- Own-input domain: none. -/
def Domain (_a : Args) : Prop := True

def RowSpec_242 (L : PoolLib) (D : DeployedIds)
    (validate_asq8 : Args → Env → Obs (Except ProgramError (Validated L))) : Prop :=
  ∀ a env, Domain a → Ref L D a env (validate_asq8 a env)


/-- The reference at a decodable request with an Err slot is exactly that Err. -/
theorem ref_slot_error (L : PoolLib) (D : DeployedIds) (vp : B32) (accts : List OwnedAccount)
    (d : Bytes) (q : L.Request) (lane : UInt8) (err : ProgramError)
    (hlen : d.length = REQUEST_BYTES) (hd : L.decodeRequest d = some q)
    (hb : (decide (L.reqProfile q ≠ PROFILE_BINDING) || decide (L.reqRelease q ≠ RELEASE_BINDING)
            || decide (L.reqPoolProgram q ≠ D.pool)) = false)
    (hl : L.outputLane (L.reqNullifier q) = some lane) :
    Ref L D ⟨vp, accts, d, .error err⟩ = RS.throw err := by
  unfold Ref
  simp only
  have c2 : (d.length != REQUEST_BYTES) = false := by simp [hlen]
  rw [c2, RS.check_false, RS.seq_pure, hd]
  simp only [RS.ofOption]
  rw [RS.bind_pure, hb, RS.check_false, RS.seq_pure, hl]
  simp only [RS.ofOption]
  rw [RS.bind_pure, RS.ofExcept_error, RS.bind_throw]

/-- Short instruction data: exactly InvalidInstructionData. -/
theorem ref_short (L : PoolLib) (D : DeployedIds) (a : Args)
    (h : a.instruction_data.length ≠ REQUEST_BYTES) : Ref L D a = RS.throw .invalidInstructionData := by
  unfold Ref
  have c : (a.instruction_data.length != REQUEST_BYTES) = true := by simp [h]
  rw [c, RS.check_true, RS.seq_throw]

/-! ## Rejection of trivial implementations

(i) a 0-byte instruction gives InvalidInstructionData; (ii) a request that the
CLOSED decoder accepts with the pinned bindings and a valid lane, but with
`current_slot = Err(UnsupportedSysvar)`, must return exactly that error before
TX2:233 is entered.  (ii) needs only that some such request exists, which holds
for the actual CLOSED decoder (the release fixtures). -/

theorem rejects_constErr (L : PoolLib) (D : DeployedIds) (d : Bytes) (q : L.Request) (lane : UInt8)
    (hlen : d.length = REQUEST_BYTES) (hd : L.decodeRequest d = some q)
    (hb : (decide (L.reqProfile q ≠ PROFILE_BINDING) || decide (L.reqRelease q ≠ RELEASE_BINDING)
            || decide (L.reqPoolProgram q ≠ D.pool)) = false)
    (hl : L.outputLane (L.reqNullifier q) = some lane) (e : ProgramError) :
    ¬ RowSpec_242 L D (constErr e) := by
  intro h
  have h1 := h ⟨zero32, [], [], .ok 0⟩ env0 trivial
  have h2 := h ⟨zero32, [], d, .error .unsupportedSysvar⟩ env0 trivial
  unfold Ref at h1 h2
  simp only at h1 h2
  have c1 : (([] : Bytes).length != REQUEST_BYTES) = true := by decide
  rw [c1, RS.check_true, RS.seq_throw] at h1
  have c2 : (d.length != REQUEST_BYTES) = false := by simp [hlen]
  rw [c2, RS.check_false, RS.seq_pure, hd] at h2
  simp only [RS.ofOption] at h2
  rw [RS.bind_pure, hb, RS.check_false, RS.seq_pure, hl] at h2
  simp only [RS.ofOption] at h2
  rw [RS.bind_pure, RS.ofExcept_error, RS.bind_throw] at h2
  simp [RS.throw, Spec.pure, constErr] at h1 h2
  rw [h1] at h2
  cases h2

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) :
    ¬ RowSpec_242 L D constAbort := by
  intro h
  have h1 := h ⟨zero32, [], [], .ok 0⟩ env0 trivial
  unfold Ref at h1
  simp only at h1
  have c1 : (([] : Bytes).length != REQUEST_BYTES) = true := by decide
  rw [c1, RS.check_true, RS.seq_throw] at h1
  simp [RS.throw, Spec.pure, constAbort] at h1

end RSL.TX2_242
