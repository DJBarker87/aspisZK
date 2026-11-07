/-
TX2:213 (and TX1:330)  programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction
Frozen signature (lib.rs:56), release features {pool-adapter}:
  pub fn process_r1_cost_probe_instruction(program_id: &Pubkey, accounts: &[AccountInfo],
      data: &[u8]) -> ProgramResult
  body: if !pool_route::admitted(data) { return Err(InvalidInstructionData) }
        return r1_pool_adapter::process(program_id, accounts, data);
(The `cfg(not(feature="pool-adapter"))` body is not compiled in the release.)
Route: guard-holding entry: ReviewedTranscription plus native cuts under
(bj)/(bl); `process` havocked over its full Result and SDK footprint.  The
entrypoint! macro's input deserialisation and Err -> u64 conversion are
outside this row (RuntimeEntrypointAdmission; Stream C ruling (c-b) shape).
Children: CLOSED pool_route::admitted (TX2:214 / TX1:331), OPEN process
(TX2:221 / TX1:333 RowSpec reference).
Own-input domain ((bf)(2)): the route-guarded child clauses only:
  (E1) on the ASQ8 route, TX2:240's (D2') Root0 clause on the entry state;
  (E2) on the stage1 route, TX1:344's own-input domain.
These are not checked by the program; they are discharged at the headline
(see RSL_INDEX.md).  No clause restricts `data`: every instruction is covered.
-/
import RSL_TX2_221
set_option autoImplicit false

namespace RSL.TX2_213
open TX2_241 (V2Lib)
open TX2_221 (Stage1 admitted stage1Route)

abbrev Args := TX2_240.Args

def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1) (a : Args) (s : SdkState) :
    Spec (Except ProgramError Unit × SdkState) :=
  if !admitted a.data then Spec.pure (.error .invalidInstructionData, s)
  else Spec.call (fun x : Args × SdkState => TX2_221.Domain V S1 x.1 x.2)
         (fun x => TX2_221.Ref L D V S1 x.1 x.2) (a, s)

def Domain (V : V2Lib) (S1 : Stage1) (a : Args) (s : SdkState) : Prop :=
  (admitted a.data = true → stage1Route a.data = false → TX2_240.Domain V a s) ∧
  (admitted a.data = true → stage1Route a.data = true → S1.dom a s)

def RowSpec_213 (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1)
    (process_r1_cost_probe_instruction :
      Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  ∀ a s env, Domain V S1 a s → Ref L D V S1 a s env (process_r1_cost_probe_instruction a s env)

/-! ## Rejection of trivial implementations -/

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1) :
    ¬ RowSpec_213 L D V S1 (fun a s => constAbort (a, s)) := by
  intro h
  have h1 := h ⟨zero32, [], []⟩ TX2_240.st0 env0
    ⟨fun h => by simp [admitted, REQUEST_MAGIC] at h, fun h => by simp [admitted, REQUEST_MAGIC] at h⟩
  unfold Ref at h1
  have ha : admitted [] = false := by decide
  rw [ha] at h1
  simp [Spec.pure, constAbort] at h1

theorem rejects_silentErr (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1)
    (e : ProgramError) (f : SdkState → SdkState) :
    ¬ RowSpec_213 L D V S1 (TX2_240.silentErr e f) := by
  intro h
  have hdom : TX2_240.Domain V ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 := by
    intro a0 a6 _ _ _ _ hl
    simp [payload, TX2_240.st0, PROOF_ACCOUNT_BYTES, AFTERSTATE_BYTES, PROOF_BYTES] at hl
  have h1 := h ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 env0
    ⟨fun _ _ => hdom, fun _ h => by simp [stage1Route, REQUEST_MAGIC] at h⟩
  unfold Ref at h1
  have ha : admitted REQUEST_MAGIC = true := by decide
  rw [ha] at h1
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at h1
  have h3 := h1.2
  have key : TX2_221.Ref L D V S1 ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩
      TX2_240.st0 = Spec.call (fun x : TX2_221.Args × SdkState => TX2_240.Domain V x.1 x.2)
        (fun x => TX2_240.Ref L D V x.1 x.2)
        (⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩, TX2_240.st0) := by
    simp [TX2_221.Ref, stage1Route, REQUEST_MAGIC]
  simp only at h3
  rw [key] at h3
  have h2 : TX2_240.Ref L D V ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩
      TX2_240.st0 env0 (TX2_240.silentErr e f ⟨zero32, List.replicate 7 TX2_240.acc0,
        REQUEST_MAGIC⟩ TX2_240.st0 env0) := h3.2
  unfold TX2_240.Ref at h2
  have hb : TX2_240.badRoute ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ = false := by
    decide
  rw [hb] at h2
  simp only [Bool.false_eq_true, if_false] at h2
  obtain ⟨rest, hr2⟩ := Spec.bind_emit_head _ _ _ _ h2
  simp [TX2_240.silentErr] at hr2

end RSL.TX2_213
