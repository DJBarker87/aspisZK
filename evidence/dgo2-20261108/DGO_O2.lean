/-
DGO_O2: obligation O2 of DGP_HostDigest section 3 is TRUE.

Target not yet established.  Core Lean only: no import, no sorry, no axiom
declaration, no premise beyond the hypotheses of O2 itself.

Exact statement (DGP_HostDigest.lean, section 3, quoted):

  def O2 : Prop :=
    ∀ (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
      (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
      (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
      (env env' : RSL.Env) (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
      (a : SCE_Experiment.Adversary Bool) (Q : Nat),
      env.pda = env'.pda → env.clock = env'.clock → env.reservation = env'.reservation →
      NNH_RecordedCharge.recorder copy
          (IDa_Deployed.deployedConfiguration
            (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env) env) err r)
          err r hashv a Q =
        NNH_RecordedCharge.recorder copy
          (IDa_Deployed.deployedConfiguration
            (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env') env') err r)
          err r hashv a Q

RSL.Env has exactly four fields (sha256, pda, clock, reservation), so env and
env' differ at most in sha256.

The host imports (Aeneas, the NNH_/LIB_/S2W_/GExq_ closure) exist only on
the build host, so this module proves O2 over faithful stand-ins.  Each
stand-in transcribes the host definition named beside it; DGO_HOST_RECIPE.md
gives the host lemmas, in order, that instantiate this proof.

  Result, Env, Digest32        Aeneas Result, RSL.Env, aspis_core.digest.Digest32
  Ops (op0 op10 op22 op38      AdapterRw.Ops; op43 is SolanaDigest::digest,
       op42 op43 op44)         op42 its clone, op38 the PDA reply
  digestInst                   AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
                               (the ONLY reader of op43 in AdapterRwModel.lean)
  hashv                        LIB_Env.hashv (reads env.sha256 only)
  fill / residual              NNH_Tx2SourceConfiguration.fill / NNH_CorrectConfiguration.residual
                               (op42, op43 := LIB_Env.hashv env, op53)
  pdaOp / select               NNH_MRegistryOps.pda / NNH_Tx2Configuration.select
                               (op38 := pda env, reserved := env.reservation)
  deployedConfiguration, fip   IDa_Deployed.deployedConfiguration, FIp_Install.configuration
                               (neither touches the adapter; boundaries are fixed)
  sdk                          DrvC_Installation.sdk (op10/op11 installed, op43 passed through)
  Call, invoke, NCode          S2W_Trace.Call / invoke / Code (done, step, call)
  stage1                       S2W_Outer.stage1_owned sdk traceEffects: direct helpers
                               on sdk (OwnedAccount.data ...), std calls, and the
                               op10 call whose dictionary is digestInst sdk
  PCode, lowerP                AspisR1PublicPreparation.PreparedHashCode.Code (digest
                               nodes carry the dictionary) and SdkD_PrepareLower.lower
  OCode                        CheckpointBytes5Effect.Code = SdkC_Source.Code
  prepare, batch, firstCode    SdkD_PrepareSource.code, GExq_BatchSource.current,
                               GExq_FirstCode.code
  child, lowerN                GExq_ChildCode.execute, GExq_OuterLower.lower
  artProgram, wrapper          ART_PartialProgram.program, ART_PartialAccount.wrapper
  account                      ART_PartialAccount.account
  bounded                      ARX_LocalCharge.bounded
  observe                      ARQ_Observer.select = Hiq_ByteSelection.select (sdk c)
  recorder                     NNH_RecordedCharge.recorder

Argument.  (1) split: the FIp configuration at env is the configuration at
env' with ONLY adapter.op43 replaced (pda/clock/reservation agree; nothing
else reads env).  (2) The recorder never reads op43: the observer and the
direct helpers do not, the trace issues no op43 call, and the only op43
carrier, the op10 dictionary, is consumed by child code whose lowering is
independent of the dictionary's digest field.  The teeth vector at the end
shows (2) is load-bearing: a trace that issued op43 would refute O2.
-/
set_option autoImplicit false

namespace DGO_O2

abbrev Bytes := List Nat
abbrev Parts := List Bytes
abbrev Digest := Bytes

inductive Err where
  | panic
  | invalid

inductive Result (α : Type) where
  | ok (a : α)
  | fail (e : Err)
  | div

def Result.bind {α β : Type} : Result α → (α → Result β) → Result β
  | .ok a, f => f a
  | .fail e, _ => .fail e
  | .div, _ => .div

instance : Monad Result where
  pure := .ok
  bind := Result.bind

/-- RSL.Env: exactly four fields. -/
structure Env where
  sha256 : List Bytes → Digest
  pda : List Bytes → Digest → Option Digest
  clock : Nat
  reservation : Bool

structure Digest32 (H : Type) where
  copy : H → Result H
  digest : H → Parts → Result Digest

structure Ops : Type 1 where
  op0 : Bytes → Bytes → Result Bool
  op10 : {H : Type} → Digest32 H → Bytes → H → Result Bool
  op22 : Nat → Result Bytes
  op38 : Parts → Digest → Result (Option Digest)
  op42 : Unit → Result Unit
  op43 : Unit → Parts → Result Digest
  op44 : Err → Result Err

/-- AspisR1CurrentCaller.Ops: supplied by `m0`, arbitrary.  op8 takes a
dictionary, as the host op6/op8/op9/op16 do; the child code never passes the
op10 dictionary to it (those ports are inlined as hash-bearing source code). -/
structure CurOps : Type 1 where
  op18 : Bytes → Result Bool
  op8 : {H : Type} → Digest32 H → Bytes → H → Result Bool

def digestInst (ops : Ops) : Digest32 Unit := ⟨ops.op42, ops.op43⟩

structure Uninstalled : Type 1 where
  adapter : Ops
  currentBase : CurOps
  reserved : Bool

structure Configuration : Type 1 where
  adapter : Ops
  currentBase : CurOps
  reserved : Bool
  boundaries : Nat

def hashv (env : Env) (parts : Parts) : Result Digest := .ok (env.sha256 parts)

def stdEq (x y : Bytes) : Result Bool := .ok (decide (x = y))

def fill (m : Uninstalled) (env : Env) : Uninstalled :=
  {m with adapter := {m.adapter with op42 := fun _ => .ok (), op43 := fun _ parts => hashv env parts}}

def residual (m : Uninstalled) (env : Env) : Uninstalled :=
  fill {m with adapter := {m.adapter with op0 := stdEq}} env

def pdaOp (env : Env) (parts : Parts) (program : Digest) : Result (Option Digest) :=
  .ok (env.pda parts program)

def select (m : Uninstalled) (env : Env) : Uninstalled :=
  {m with adapter := {m.adapter with op38 := pdaOp env}, reserved := env.reservation}

def deployedConfiguration (m : Uninstalled) (_err : Err) (r : Bool) : Configuration :=
  ⟨m.adapter, m.currentBase, m.reserved, if r then 1 else 0⟩

def fip (_err : Err) (c : Configuration) (_r : Bool) : Configuration :=
  {c with boundaries := c.boundaries + 1}

def sdk (c : Configuration) : Ops :=
  {c.adapter with op10 := fun D proof h => c.currentBase.op8 D proof h}

/-! ## Native trace syntax (S2W_Trace) -/

inductive Call : Type → Type 1 where
  | op0 (x y : Bytes) : Call Bool
  | op10 {H : Type} (D : Digest32 H) (proof : Bytes) (h : H) : Call Bool
  | op22 (n : Nat) : Call Bytes
  | op43 (parts : Parts) : Call Digest
  | op44 (e : Err) : Call Err

def invoke (ops : Ops) : {A : Type} → Call A → Result A
  | _, .op0 x y => ops.op0 x y
  | _, .op10 D proof h => ops.op10 D proof h
  | _, .op22 n => ops.op22 n
  | _, .op43 parts => ops.op43 () parts
  | _, .op44 e => ops.op44 e

inductive NCode (A : Type) : Type 1 where
  | done (a : A)
  | step {B : Type} (r : Result B) (k : B → NCode A)
  | call {B : Type} (c : Call B) (k : B → NCode A)

def NCode.bind {A B : Type} : NCode A → (A → NCode B) → NCode B
  | .done a, f => f a
  | .step r k, f => .step r (fun b => NCode.bind (k b) f)
  | .call c k, f => .call c (fun b => NCode.bind (k b) f)

instance : Monad NCode where
  pure := .done
  bind := NCode.bind

def NCode.lift {A : Type} (r : Result A) : NCode A := .step r .done
def NCode.perform {A : Type} (c : Call A) : NCode A := .call c .done

/-- AdapterRw helper read directly on the sdk (OwnedAccount.data style). -/
def dataOf (ops : Ops) (n : Nat) : Result Bytes := ops.op22 n

/-- S2W_Outer.stage1_owned: helpers on `ops`, a std call, the op10 call with
dictionary `digestInst ops`, the error mapper op44. -/
def stage1 (ops : Ops) (input : Bytes) : NCode Bool := do
  let stored ← NCode.lift (dataOf ops input.length)
  let same ← NCode.perform (.op0 stored input)
  if same then
    let accepted ← NCode.perform (.op10 (digestInst ops) input ())
    if accepted then pure true
    else
      let _ ← NCode.perform (.op44 .invalid)
      pure false
  else pure false

/-! ## Hash-bearing child syntax -/

inductive PCode (A : Type) : Type 1 where
  | done (a : A)
  | step {B : Type} (r : Result B) (k : B → PCode A)
  | digest {H : Type} (D : Digest32 H) (h : H) (parts : Parts) (k : Digest → PCode A)

inductive OCode (A : Type) : Type 1 where
  | done (a : A)
  | step {B : Type} (r : Result B) (k : B → OCode A)
  | read (parts : Parts) (k : Digest → OCode A)

def OCode.bind {A B : Type} : OCode A → (A → OCode B) → OCode B
  | .done a, f => f a
  | .step r k, f => .step r (fun b => OCode.bind (k b) f)
  | .read parts k, f => .read parts (fun d => OCode.bind (k d) f)

/-- SdkD_PrepareLower.lower: the dictionary of a digest node is dropped. -/
def lowerP {A : Type} : PCode A → OCode A
  | .done a => .done a
  | .step r k => .step r (fun b => lowerP (k b))
  | .digest _ _ parts k => .read parts (fun d => lowerP (k d))

/-- SdkD_PrepareSource.code: a digest node carrying D, then a use of D's
copy instance (the only dictionary field the source reads besides digest). -/
def prepare {H : Type} (D : Digest32 H) (h : H) (proof : Bytes) : PCode Bool :=
  .digest D h [proof] (fun d => .step (D.copy h) (fun _ => .done (decide (d.length = 32))))

/-- GExq_BatchSource.current: rebuilds E from D, reads through `read`. -/
def batch {H : Type} (D : Digest32 H) (h : H) (proof root : Bytes) : OCode Bool :=
  .read [proof, root] (fun d =>
    .step ((⟨D.copy, D.digest⟩ : Digest32 H).copy h) (fun _ => .done (decide (d = root))))

/-- GExq_FirstCode.code. -/
def firstCode {H : Type} (base : CurOps) (D : Digest32 H) (h : H) (proof : Bytes) : OCode Bool :=
  OCode.bind (lowerP (prepare D h proof)) (fun prepared =>
    if prepared then
      OCode.bind (.step (base.op18 proof) .done) (fun ok =>
        if ok then batch D h proof [] else .done false)
    else .done false)

/-- GExq_ChildCode.execute: op10 runs the inlined child; every other call is
the sdk reply. -/
def child (c : Configuration) : {B : Type} → Call B → OCode B
  | _, .op10 D proof h => firstCode c.currentBase D h proof
  | _, .op0 x y => .step (invoke (sdk c) (.op0 x y)) .done
  | _, .op22 n => .step (invoke (sdk c) (.op22 n)) .done
  | _, .op43 parts => .step (invoke (sdk c) (.op43 parts)) .done
  | _, .op44 e => .step (invoke (sdk c) (.op44 e)) .done

/-- GExq_OuterLower.lower. -/
def lowerN {A : Type} (impl : {B : Type} → Call B → OCode B) : NCode A → OCode A
  | .done a => .done a
  | .step r k => .step r (fun b => lowerN impl (k b))
  | .call op k => OCode.bind (impl op) (fun b => lowerN impl (k b))

/-! ## Oracle programs, account, recorder -/

inductive Program (A : Type) : Type where
  | done (a : A)
  | ask (q : Bytes) (k : Digest → Program A)

def Program.bind {A B : Type} : Program A → (A → Program B) → Program B
  | .done a, f => f a
  | .ask q k, f => .ask q (fun s => Program.bind (k s) f)

def flatten (parts : Parts) : Bytes := parts.flatten

abbrev Log := List (Parts × Result Digest)

/-- ART_PartialProgram.program: status of hashv, answer from the oracle. -/
def artProgram {A : Type} (hv : Parts → Result Digest) : OCode A → Log → Program (Result A × Log)
  | .done a, before => .done (.ok a, before)
  | .step r k, before =>
    match r with
    | .ok b => artProgram hv (k b) before
    | .fail e => .done (.fail e, before)
    | .div => .done (.div, before)
  | .read parts k, before => .ask (flatten parts) fun value =>
    match hv parts with
    | .ok _ => artProgram hv (k value) (before ++ [(parts, .ok value)])
    | .fail e => .done (.fail e, before ++ [(parts, .fail e)])
    | .div => .done (.div, before ++ [(parts, .div)])

def wrapper {V : Type} (hv : Parts → Result Digest) (code : OCode V) : Program (Result V) :=
  Program.bind (artProgram hv code []) (fun raw => .done raw.1)

/-- ART_PartialAccount.account: adversary choice, then the wrapped source. -/
def account (c : Configuration) (hv : Parts → Result Digest) (a : Program Bytes) :
    Program (Bytes × Result Bool) :=
  Program.bind a (fun i =>
    Program.bind (wrapper hv (lowerN (child c) (stage1 (sdk c) i))) (fun out => .done (i, out)))

def bounded {A : Type} : Program A → Nat → Program (Option A)
  | .done a, _ => .done (some a)
  | .ask _ _, 0 => .done none
  | .ask q k, n + 1 => .ask q (fun s => bounded (k s) n)

/-- ARQ_Observer.select: AdapterRw helpers on the sdk only. -/
def observe (ops : Ops) (out : Bytes × Result Bool) : Bytes :=
  match dataOf ops out.1.length with
  | .ok b => b
  | _ => []

def recorderAt (c : Configuration) (hv : Parts → Result Digest) (a : Program Bytes) (Q : Nat) :
    Program (Option (Bytes × Result Bool) × Bytes) :=
  Program.bind (bounded (account c hv a) Q) (fun v =>
    .done (v, match v with
      | some out => observe (sdk c) out
      | none => []))

/-- NNH_RecordedCharge.recorder: the FIp configuration is built inside. -/
def recorder (base : Configuration) (err : Err) (r : Bool) (hv : Parts → Result Digest)
    (a : Program Bytes) (Q : Nat) := recorderAt (fip err base r) hv a Q

/-- O2, transcribed. -/
def O2 : Prop :=
  ∀ (m0 : Uninstalled) (err : Err) (r : Bool) (env env' : Env)
    (hv : Parts → Result Digest) (a : Program Bytes) (Q : Nat),
    env.pda = env'.pda → env.clock = env'.clock → env.reservation = env'.reservation →
    recorder (deployedConfiguration (select (residual m0 env) env) err r) err r hv a Q =
      recorder (deployedConfiguration (select (residual m0 env') env') err r) err r hv a Q

/-! ## Step 1: the configurations differ only in adapter.op43 -/

def withDigest (c : Configuration) (o : Unit → Parts → Result Digest) : Configuration :=
  {c with adapter := {c.adapter with op43 := o}}

theorem split (m0 : Uninstalled) (err : Err) (r : Bool) (env env' : Env)
    (hp : env.pda = env'.pda) (hc : env.clock = env'.clock)
    (hr : env.reservation = env'.reservation) :
    fip err (deployedConfiguration (select (residual m0 env) env) err r) r =
      withDigest (fip err (deployedConfiguration (select (residual m0 env') env') err r) r)
        (fun _ parts => hashv env parts) := by
  obtain ⟨s, p, k, v⟩ := env
  obtain ⟨s', p', k', v'⟩ := env'
  dsimp only at hp hc hr
  subst hp hc hr
  rfl

theorem sdk_withDigest (c : Configuration) (o : Unit → Parts → Result Digest) :
    sdk (withDigest c o) = {sdk c with op43 := o} := rfl

/-! ## Step 2: the native trace agrees up to the op10 dictionary's digest -/

/-- Calls that are not op43. -/
def NotDigest : {B : Type} → Call B → Prop
  | _, .op43 _ => False
  | _, .op0 _ _ => True
  | _, .op10 _ _ _ => True
  | _, .op22 _ => True
  | _, .op44 _ => True

inductive CallSim : {B : Type} → Call B → Call B → Prop where
  | same {B : Type} (c : Call B) (h : NotDigest c) : CallSim c c
  | op10 {H : Type} (D1 D2 : Digest32 H) (hc : D1.copy = D2.copy) (proof : Bytes) (h : H) :
      CallSim (.op10 D1 proof h) (.op10 D2 proof h)

inductive Sim {A : Type} : NCode A → NCode A → Prop where
  | done (a : A) : Sim (.done a) (.done a)
  | step {B : Type} (r : Result B) (k1 k2 : B → NCode A) (hk : ∀ b, Sim (k1 b) (k2 b)) :
      Sim (.step r k1) (.step r k2)
  | call {B : Type} (c1 c2 : Call B) (k1 k2 : B → NCode A) (hc : CallSim c1 c2)
      (hk : ∀ b, Sim (k1 b) (k2 b)) : Sim (.call c1 k1) (.call c2 k2)

theorem sim_bind {A B : Type} {p q : NCode A} {f g : A → NCode B} (h : Sim p q)
    (hk : ∀ a, Sim (f a) (g a)) : Sim (p >>= f) (q >>= g) := by
  induction h with
  | done a => exact hk a
  | step r k1 k2 _ ih => exact .step r _ _ (fun b => ih b)
  | call c1 c2 k1 k2 hc _ ih => exact .call c1 c2 _ _ hc (fun b => ih b)

theorem sim_pure {A : Type} (a : A) : Sim (pure a : NCode A) (pure a) := .done a

theorem sim_lift {A : Type} (r : Result A) : Sim (NCode.lift r) (NCode.lift r) :=
  .step r _ _ (fun b => .done b)

theorem sim_perform {A : Type} {c1 c2 : Call A} (h : CallSim c1 c2) :
    Sim (NCode.perform c1) (NCode.perform c2) :=
  .call c1 c2 _ _ h (fun b => .done b)

/-- Host analogue: unfold S2W_Outer.stage1_owned / stage2_owned and close by
the GExq_OuterGoodStage1 tactic loop with sim_* in place of *_good. -/
theorem stage1_sim (o : Unit → Parts → Result Digest) (ops : Ops) (input : Bytes) :
    Sim (stage1 {ops with op43 := o} input) (stage1 ops input) := by
  unfold stage1
  refine sim_bind (sim_lift _) (fun stored => ?_)
  refine sim_bind (sim_perform (.same _ trivial)) (fun same => ?_)
  split
  · refine sim_bind (sim_perform (.op10 (digestInst {ops with op43 := o}) (digestInst ops) rfl input ()))
      (fun accepted => ?_)
    split
    · exact sim_pure _
    · exact sim_bind (sim_perform (.same _ trivial)) (fun _ => sim_pure _)
  · exact sim_pure _

theorem lowerN_sim {A : Type} (impl1 impl2 : {B : Type} → Call B → OCode B)
    (himpl : ∀ {B : Type} (x y : Call B), CallSim x y → impl1 x = impl2 y)
    {c1 c2 : NCode A} (h : Sim c1 c2) : lowerN impl1 c1 = lowerN impl2 c2 := by
  induction h with
  | done a => rfl
  | step r k1 k2 _ ih =>
    simp only [lowerN]
    congr 1
    funext b
    exact ih b
  | call c1 c2 k1 k2 hc _ ih =>
    simp only [lowerN]
    rw [himpl c1 c2 hc]
    congr 1
    funext b
    exact ih b

/-! ## Step 3: the lowered child code ignores the dictionary's digest -/

inductive DSim {A : Type} : PCode A → PCode A → Prop where
  | done (a : A) : DSim (.done a) (.done a)
  | step {B : Type} (r : Result B) (k1 k2 : B → PCode A) (hk : ∀ b, DSim (k1 b) (k2 b)) :
      DSim (.step r k1) (.step r k2)
  | digest {H : Type} (D1 D2 : Digest32 H) (h : H) (parts : Parts) (k1 k2 : Digest → PCode A)
      (hk : ∀ d, DSim (k1 d) (k2 d)) : DSim (.digest D1 h parts k1) (.digest D2 h parts k2)

theorem lowerP_dsim {A : Type} {c1 c2 : PCode A} (h : DSim c1 c2) : lowerP c1 = lowerP c2 := by
  induction h with
  | done a => rfl
  | step r k1 k2 _ ih =>
    simp only [lowerP]
    congr 1
    funext b
    exact ih b
  | digest D1 D2 h parts k1 k2 _ ih =>
    simp only [lowerP]
    congr 1
    funext d
    exact ih d

/-- Host analogue: the S1PrepareCode.dictionary_irrelevant proof script with
`lowerP` for `oracleProgram` (same leaves: identical steps by rfl, digest
nodes by DSim.digest, the claim step by claimPublic_digest_irrelevant). -/
theorem prepare_dsim {H : Type} (D1 D2 : Digest32 H) (hc : D1.copy = D2.copy) (h : H)
    (proof : Bytes) : DSim (prepare D1 h proof) (prepare D2 h proof) := by
  unfold prepare
  refine .digest D1 D2 h _ _ _ (fun d => ?_)
  rw [hc]
  exact .step _ _ _ (fun _ => .done _)

theorem batch_eq {H : Type} (D1 D2 : Digest32 H) (hc : D1.copy = D2.copy) (h : H)
    (proof root : Bytes) : batch D1 h proof root = batch D2 h proof root := by
  unfold batch
  dsimp only
  rw [hc]

theorem firstCode_eq {H : Type} (base : CurOps) (D1 D2 : Digest32 H) (hc : D1.copy = D2.copy)
    (h : H) (proof : Bytes) : firstCode base D1 h proof = firstCode base D2 h proof := by
  unfold firstCode
  rw [lowerP_dsim (prepare_dsim D1 D2 hc h proof), batch_eq D1 D2 hc h proof []]

theorem child_sim (c : Configuration) (o : Unit → Parts → Result Digest) :
    ∀ {B : Type} (x y : Call B), CallSim x y → child (withDigest c o) x = child c y := by
  intro B x y h
  cases h with
  | same _ hnd =>
    cases x with
    | op43 parts => exact absurd hnd id
    | op0 _ _ => rfl
    | op10 _ _ _ => rfl
    | op22 _ => rfl
    | op44 _ => rfl
  | op10 D1 D2 hc proof h =>
    exact firstCode_eq c.currentBase D1 D2 hc h proof

/-! ## Step 4: assembly -/

theorem account_withDigest (c : Configuration) (o : Unit → Parts → Result Digest)
    (hv : Parts → Result Digest) (a : Program Bytes) :
    account (withDigest c o) hv a = account c hv a := by
  unfold account
  congr 1
  funext i
  rw [sdk_withDigest, lowerN_sim (child (withDigest c o)) (child c) (child_sim c o)
    (stage1_sim o (sdk c) i)]

theorem observe_op43 (ops : Ops) (o : Unit → Parts → Result Digest) (out : Bytes × Result Bool) :
    observe {ops with op43 := o} out = observe ops out := rfl

theorem recorderAt_withDigest (c : Configuration) (o : Unit → Parts → Result Digest)
    (hv : Parts → Result Digest) (a : Program Bytes) (Q : Nat) :
    recorderAt (withDigest c o) hv a Q = recorderAt c hv a Q := by
  unfold recorderAt
  rw [account_withDigest, sdk_withDigest]
  rfl

theorem o2 : O2 := by
  intro m0 err r env env' hv a Q hp hc hr
  unfold recorder
  rw [split m0 err r env env' hp hc hr, recorderAt_withDigest]

/-! ## Teeth: O2 fails for a trace that issues op43

Same configurations and recorder, but the trace performs Call.op43 and
branches on the reply.  Two envs that differ only in sha256 then give
different recorders, so the op43-freeness of the trace (step 2) carries O2. -/

def leakyStage1 (_ops : Ops) (_input : Bytes) : NCode Bool := do
  let d ← NCode.perform (.op43 [[1]])
  pure (decide (d = [0]))

def leakyRecorder (base : Configuration) (err : Err) (r : Bool) (hv : Parts → Result Digest)
    (a : Program Bytes) (Q : Nat) : Program (Option (Bytes × Result Bool)) :=
  let c := fip err base r
  bounded (Program.bind a (fun i =>
    Program.bind (wrapper hv (lowerN (child c) (leakyStage1 (sdk c) i)))
      (fun out => .done (i, out)))) Q

def evalP {A : Type} (oracle : Bytes → Digest) : Program A → A
  | .done a => a
  | .ask q k => evalP oracle (k (oracle q))

def accepted : Option (Bytes × Result Bool) → Bool
  | some (_, .ok true) => true
  | _ => false

def m0Teeth : Uninstalled :=
  ⟨⟨stdEq, fun _ _ _ => .ok true, fun _ => .ok [], fun _ _ => .ok none, fun _ => .ok (),
    fun _ _ => .ok [], fun e => .ok e⟩,
   ⟨fun _ => .ok true, fun _ _ _ => .ok true⟩, false⟩

def env0 : Env := ⟨fun _ => [0], fun _ _ => none, 0, true⟩
def env1 : Env := ⟨fun _ => [1], fun _ _ => none, 0, true⟩

theorem leaky_differs :
    leakyRecorder (deployedConfiguration (select (residual m0Teeth env0) env0) .panic true) .panic true
        (fun _ => .ok []) (.done []) 4 ≠
      leakyRecorder (deployedConfiguration (select (residual m0Teeth env1) env1) .panic true) .panic true
        (fun _ => .ok []) (.done []) 4 := by
  intro same
  have h := congrArg (fun p => accepted (evalP (fun _ => []) p)) same
  exact Bool.noConfusion h

#print axioms split
#print axioms sdk_withDigest
#print axioms stage1_sim
#print axioms lowerN_sim
#print axioms lowerP_dsim
#print axioms prepare_dsim
#print axioms batch_eq
#print axioms firstCode_eq
#print axioms child_sim
#print axioms account_withDigest
#print axioms recorderAt_withDigest
#print axioms o2
#print axioms leaky_differs

end DGO_O2
