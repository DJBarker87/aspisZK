/-
TX2:221 (and TX1:333)  programs/r1-cost-probe/src/r1_pool_adapter.rs::process
Frozen signature (r1_pool_adapter.rs:950):
  pub(super) fn process(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8])
      -> ProgramResult
Route: guard-holding dispatcher: ReviewedTranscription plus native cuts under
(bj)/(bl); stage1/stage2 are havocked over their full Result and SDK footprint.
Children: OPEN TX1:344 stage1 (law `S1.ref`, instantiated with RSL_TX1_344.Ref
in RSL_TX1_333), OPEN TX2:240 stage2 (RowSpec_240 reference).  The lifecycle
arms (data[0] in {4,5,6}) are excluded by the own-input domain.
The two ledger rows are the same function in the two transactions; both carry
this one full statement (RowSpec_221 = RowSpec_333 after instantiation), since
a row that covered only its own transaction's route would be weaker than the
function's obligation.
Own-input domain ((bf)(2)), caller clauses of TX2:213 / TX1:330:
  (P1) `pool_route::admitted(data)` (CLOSED TX2:214), which TX2:213 checks;
  (P2) on the stage2 route, TX2:240's (D2');
  (P3) on the stage1 route, TX1:344's own-input domain.
-/
import RSL_TX2_240
set_option autoImplicit false

namespace RSL.TX2_221
open TX2_241 (V2Lib)

abbrev Args := TX2_240.Args

/-- `pool_route::admitted` (CLOSED TX1:331 / TX2:214, NHJ_RoutePacket). -/
def admitted (data : Bytes) : Bool :=
  data == [3, 10] || data == [3, 11] || data.take 4 == REQUEST_MAGIC

def stage1Route (data : Bytes) : Bool := data == [3, 10] || data == [3, 11]

/-- The stage1 child as it enters this spec: its own-input domain and its
reference relation over the SDK parent state (TX1:344). -/
structure Stage1 where
  dom : Args → SdkState → Prop
  ref : Args → SdkState → Spec (Except ProgramError Unit × SdkState)

/-- The SDK parent state threads through as a pair argument of `Spec.call`. -/
def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1) (a : Args) (s : SdkState) :
    Spec (Except ProgramError Unit × SdkState) :=
  match a.data.head? with
  | some 4 | some 5 | some 6 => fun _ _ => False   -- lifecycle arms: excluded by (P1)
  | _ =>
    if stage1Route a.data then
      Spec.call (fun x : Args × SdkState => S1.dom x.1 x.2) (fun x => S1.ref x.1 x.2) (a, s)
    else
      Spec.call (fun x : Args × SdkState => TX2_240.Domain V x.1 x.2)
        (fun x => TX2_240.Ref L D V x.1 x.2) (a, s)

def Domain (V : V2Lib) (S1 : Stage1) (a : Args) (s : SdkState) : Prop :=
  admitted a.data = true ∧
  (stage1Route a.data = false → TX2_240.Domain V a s) ∧
  (stage1Route a.data = true → S1.dom a s)

def RowSpec_221 (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1)
    (process : Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  ∀ a s env, Domain V S1 a s → Ref L D V S1 a s env (process a s env)

/-! ## Rejection of trivial implementations (any stage1 law) -/

theorem rejects_silentErr (L : PoolLib) (D : DeployedIds) (V : V2Lib) (S1 : Stage1)
    (e : ProgramError) (f : SdkState → SdkState) :
    ¬ RowSpec_221 L D V S1 (TX2_240.silentErr e f) := by
  intro h
  have hdom : TX2_240.Domain V ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 := by
    intro a0 a6 _ _ _ _ hl
    simp [payload, TX2_240.st0, PROOF_ACCOUNT_BYTES, AFTERSTATE_BYTES, PROOF_BYTES] at hl
  have h1 := h ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 env0
    ⟨by decide, fun _ => hdom, fun h => by simp [stage1Route, REQUEST_MAGIC] at h⟩
  have key : Ref L D V S1 ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 =
      Spec.call (fun x : Args × SdkState => TX2_240.Domain V x.1 x.2)
        (fun x => TX2_240.Ref L D V x.1 x.2)
        (⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩, TX2_240.st0) := by
    simp [Ref, stage1Route, REQUEST_MAGIC]
  rw [key] at h1
  have h2 : TX2_240.Ref L D V ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 env0
      (TX2_240.silentErr e f ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ TX2_240.st0 env0) :=
    h1.2
  unfold TX2_240.Ref at h2
  have hb : TX2_240.badRoute ⟨zero32, List.replicate 7 TX2_240.acc0, REQUEST_MAGIC⟩ = false := by
    decide
  rw [hb] at h2
  simp only [Bool.false_eq_true, if_false] at h2
  obtain ⟨rest, hr2⟩ := Spec.bind_emit_head _ _ _ _ h2
  simp [TX2_240.silentErr] at hr2

end RSL.TX2_221
