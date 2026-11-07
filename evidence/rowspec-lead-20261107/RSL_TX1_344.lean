/-
TX1:344  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1
Frozen signature (r1_pool_adapter_owned.rs:447):
  pub(super) fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8])
      -> ProgramResult
Route: guard-holding wrapper (snapshot guards, the RefMut for the copy):
ReviewedTranscription plus native cuts under (bj)/(bl); stage1_owned is
havocked over its full Result in the harness and composed here by its RowSpec.
Children: CLOSED snapshot (TX1:343) x3 in index order, OPEN stage1_owned
(TX1:345 reference at SAME arguments), SDK try_borrow_mut_data (NLF_ law,
(be)(2)), `copy_from_slice` (std, (au): panics iff lengths differ).
cu-profiling off: no log line.
State and effects, in order: three snapshot acquire/release pairs; on Ok an
exclusive acquire of accounts[2]'s data cell (Err -> AccountBorrowFailed,
returned), then one `write` of the checkpoint bytes, then the guard release
at the end of the statement.  Frame: no other cell's payload changes; on every
Err arm no payload changes.
Own-input domain ((bf)(2)): none.
-/
import RSL_TX1_345
import RSL_TX2_221
set_option autoImplicit false

namespace RSL.TX1_344
open TX1_345 (S1Lib)

abbrev Args := TX2_240.Args

def snapLens : List (Nat × Nat) :=
  [(PROOF_ACCOUNT_BYTES, PROOF_ACCOUNT_BYTES), (STATEMENT_BYTES, STATEMENT_BYTES),
   (CHECKPOINT_BYTES, CHECKPOINT_BYTES)]

def badRoute (a : Args) : Bool :=
  !(a.data == [3, 10] || a.data == [3, 11]) || a.accounts.length != 3

/-- The copy statement, line 457, on the state after stage1_owned. -/
def copyStep (acc2 : AccountInfo) (ck : Bytes) (s : SdkState) :
    Spec (Except ProgramError Unit × SdkState) :=
  Spec.bind (acquire acc2 .exclusive s) fun r =>
  match r with
  | (.error e, s2) => Spec.pure (.error e, s2)
  | (.ok t, s2) =>
    if ck.length != (payload acc2 s2).length then Spec.panic
    else
      Spec.bind (Spec.emit (.write acc2.cell ck)) fun _ =>
      let c := s2.cells acc2.cell
      Spec.bind (release acc2 t .exclusive (s2.put acc2.cell { c with payload := ck })) fun s4 =>
      Spec.pure (.ok (), s4)

def Ref (V : VLib) (P : PreparedNew V) (C : S1Lib V) (a : Args) (s : SdkState) :
    Spec (Except ProgramError Unit × SdkState) :=
  if badRoute a then Spec.pure (.error .invalidInstructionData, s) else
  Spec.bind (TX2_240.snapAll a.accounts snapLens s) fun r =>
  Spec.bind (Spec.call TX1_345.Domain (TX1_345.Ref V P C) ⟨a.program_id, r.1, a.data⟩) fun res =>
  match res with
  | .error e => Spec.pure (.error e, r.2)
  | .ok ck =>
    match a.accounts[2]? with
    | none => Spec.panic
    | some acc2 => copyStep acc2 ck r.2

def Domain (_a : Args) (_s : SdkState) : Prop := True

def RowSpec_344 (V : VLib) (P : PreparedNew V) (C : S1Lib V)
    (stage1 : Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  ∀ a s env, Domain a s → Ref V P C a s env (stage1 a s env)

/-- The stage1 child packet as TX2:221 / TX1:333 consume it. -/
def asStage1 (V : VLib) (P : PreparedNew V) (C : S1Lib V) : TX2_221.Stage1 :=
  ⟨Domain, Ref V P C⟩

/-! ## Rejection of trivial implementations: a bad route forces exactly
(Err(InvalidInstructionData), s) with no event (rejects constant abort); an
admitted route with three accounts must begin with the snapshot acquire event
(rejects every silent constant Err). -/

theorem rejects_silentErr (V : VLib) (P : PreparedNew V) (C : S1Lib V) (e : ProgramError)
    (f : SdkState → SdkState) : ¬ RowSpec_344 V P C (TX2_240.silentErr e f) := by
  intro h
  have h1 := h ⟨zero32, [TX2_240.acc0, TX2_240.acc0, TX2_240.acc0], [3, 10]⟩ TX2_240.st0 env0 trivial
  unfold Ref at h1
  have hb : badRoute ⟨zero32, [TX2_240.acc0, TX2_240.acc0, TX2_240.acc0], [3, 10]⟩ = false := by decide
  rw [hb] at h1
  simp only [Bool.false_eq_true, if_false] at h1
  have := Spec.bind_nonempty _ _ _ _ (fun o' h' => by
    unfold TX2_240.snapAll at h'
    exact Spec.bind_nonempty _ _ _ _ (fun o'' h'' => snapshot_nonempty _ _ _ _ _ _ h'') h') h1
  exact this rfl

theorem rejects_constAbort (V : VLib) (P : PreparedNew V) (C : S1Lib V) :
    ¬ RowSpec_344 V P C (fun a s => constAbort (a, s)) := by
  intro h
  have h1 := h ⟨zero32, [], []⟩ TX2_240.st0 env0 trivial
  unfold Ref at h1
  have hb : badRoute ⟨zero32, [], []⟩ = true := by decide
  rw [hb] at h1
  simp [Spec.pure, constAbort] at h1

end RSL.TX1_344
