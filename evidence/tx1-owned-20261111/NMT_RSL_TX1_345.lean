/-
TX1:345  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned
Frozen signature (r1_pool_adapter_owned.rs:376):
  fn stage1_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8])
      -> Result<Vec<u8>, ProgramError>
Route: emitted body under (bm).
Children: CLOSED require_distinct_accounts TX1:339, require_readonly_buffer
TX1:340, require_verifier_checkpoint TX1:341, OwnedAccount::data TX1:335,
require_zero TX1:342, decode_public_statement_box TX1:332 (decoder then Box),
validate_pool_v1_pair_forest_terminal_statement_v1 TX1:276,
PoolV1PairForestTerminalStatementV1::common TX1:267,
encode_pool_v1_pair_verified_afterstate_v1 TX1:278 (returns [u8; 688], no
allocation), Variant::tag TX1:173 (S2 = 2), semantic_public TX1:268; OPEN
first_decoded TX1:328 (RowSpec_328 reference at SAME arguments:
statement.semantic_public(), the public snapshot bytes, proof[688..58295],
data[1] as usize).
Own-input domain ((bf)(2)): none.  TX1:328's clause `publicDom
(semantic_public statement)` is NOT a hypothesis here: it must be derived from
the CLOSED decode/validate laws at the decoded statement.  If those laws do
not export it, that is a missing child lemma under (aq)(3), not a domain clause.
Effects: the statement Box allocation; then first_decoded's events; abort =
prefix.  The returned Vec is the checkpoint image written by TX1:344.
-/
import NMT_RSL_TX1_328
import NMT_RSL_Pool
set_option autoImplicit false

namespace RSL.TX1_345

structure S1Lib (V : VLib) where
  Statement : Type
  /-- decoder inside decode_public_statement_box (CLOSED TX1:332, NFY_Part058). -/
  decodeStatement : Bytes → Option Statement
  /-- `validate_..._statement_v1(..).is_ok()` (CLOSED TX1:276, NFY_Part031). -/
  validateStatement : Statement → Bool
  /-- encode_pool_v1_pair_verified_afterstate_v1 at
  statement.common().lane_transition.candidate_afterstate (CLOSED TX1:278 ∘ TX1:267);
  `none` = encoder Err. -/
  encodeCandidate : Statement → Option Bytes
  /-- statement.semantic_public() (CLOSED TX1:268, NJB_SemanticPublic). -/
  semanticPublic : Statement → V.Public

def S2_TAG : UInt8 := 2

structure Args where
  program_id : B32
  accounts : List OwnedAccount
  data : Bytes

def badRoute (a : Args) : Bool :=
  !(a.data == [3, 10] || a.data == [3, 11]) || a.accounts.length != 3

def body (V : VLib) (P : PreparedNew V) (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) :
    RS Bytes :=
  RS.seq (RS.ofExcept (requireDistinct [p, pub, ck])) <|
  RS.seq (RS.ofExcept (readonlyBuffer p)) <|
  RS.seq (RS.ofExcept (readonlyBuffer pub)) <|
  RS.seq (RS.ofExcept (verifierCheckpoint ck a.program_id true)) <|
  RS.bind (RS.ofExcept ck.data) fun checkpointData =>
  RS.seq (RS.ofExcept (requireZero checkpointData)) <|
  RS.bind (RS.ofExcept pub.data) fun publicData =>
  RS.bind (RS.ofOption (C.decodeStatement publicData) .invalidAccountData) fun st =>
  RS.seq (RS.lift Spec.alloc) <|
  RS.seq (RS.check (!C.validateStatement st) .invalidAccountData) <|
  RS.bind (RS.ofOption (C.encodeCandidate st) .invalidAccountData) fun candidate =>
  RS.bind (RS.ofExcept p.data) fun proofData =>
  RS.seq (RS.check (proofData.length != PROOF_ACCOUNT_BYTES
                    || proofData.take AFTERSTATE_BYTES != candidate
                    || proofData.getD (AFTERSTATE_BYTES + 8) 0 != S2_TAG) .invalidAccountData) <|
  RS.bind (Spec.call (TX1_328.Domain V) (TX1_328.Ref V P)
            ⟨C.semanticPublic st, publicData, slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
             (a.data.getD 1 0).toNat⟩) fun checkpoint =>
  RS.seq (RS.check (checkpoint.length != checkpointData.length) .invalidAccountData) <|
  RS.pure checkpoint

def Ref (V : VLib) (P : PreparedNew V) (C : S1Lib V) (a : Args) : RS Bytes :=
  if badRoute a then RS.throw .invalidInstructionData else
  match a.accounts with
  | [p, pub, ck] => body V P C a p pub ck
  | _ => RS.lift Spec.panic   -- unreachable: length is 3 here

def Domain (_a : Args) : Prop := True

def RowSpec_345 (V : VLib) (P : PreparedNew V) (C : S1Lib V)
    (stage1_owned : Args → Env → Obs (Except ProgramError Bytes)) : Prop :=
  ∀ a env, Domain a → Ref V P C a env (stage1_owned a env)

/-! ## Rejection of trivial implementations: wrong data forces
InvalidInstructionData; three accounts with duplicate keys force
InvalidArgument (require_distinct_accounts runs first).  No constant Err
survives; the first input rejects a constant abort. -/

def acct0 : OwnedAccount := ⟨zero32, zero32, false, false, false, .ok 0, .ok []⟩

theorem rejects_constErr (V : VLib) (P : PreparedNew V) (C : S1Lib V) (e : ProgramError) :
    ¬ RowSpec_345 V P C (constErr e) := by
  intro h
  have h1 := h ⟨zero32, [], []⟩ env0 trivial
  have h2 := h ⟨zero32, [acct0, acct0, acct0], [3, 10]⟩ env0 trivial
  unfold Ref at h1 h2
  have b1 : badRoute ⟨zero32, [], []⟩ = true := by decide
  have b2 : badRoute ⟨zero32, [acct0, acct0, acct0], [3, 10]⟩ = false := by decide
  rw [b1] at h1
  rw [b2] at h2
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  unfold body at h2
  have d : requireDistinct [acct0, acct0, acct0] = .error .invalidArgument := by
    simp [requireDistinct, distinctKeys, acct0]
  rw [d, RS.ofExcept_error, RS.seq_throw] at h2
  simp [RS.throw, Spec.pure, constErr] at h1 h2
  rw [h1] at h2
  cases h2

theorem rejects_constAbort (V : VLib) (P : PreparedNew V) (C : S1Lib V) :
    ¬ RowSpec_345 V P C constAbort := by
  intro h
  have h1 := h ⟨zero32, [], []⟩ env0 trivial
  unfold Ref at h1
  have b1 : badRoute ⟨zero32, [], []⟩ = true := by decide
  rw [b1] at h1
  simp [RS.throw, Spec.pure, constAbort] at h1

end RSL.TX1_345
