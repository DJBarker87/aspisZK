/-
DGP_DigestMirror: core-Lean mirror of the P2 digest obligation (NNH_ run 5).

Target not yet established.  Core Lean only; no import, no sorry, no axiom
declaration.  Every definition below transcribes, with the carriers made
abstract, a host definition quoted in DGP_DECISION.md section 1:

  Res                 Aeneas `Result` (ok / fail / div)
  digest              S2W_DigestExtraction.digest  (bind hashv, then toBytes = ok)
  RuntimeSyscall      S2Z.Oracle.RuntimeSyscall (the field of
                      S2W_ExtractionBoundary.RuntimeSyscall.returningValue)
  P1                  S2Z.Oracle.P1Realization
  DigestSource        S2W_DigestExtraction.AeneasExtraction.digestSource
  libHashv            LIB_Env.hashv (op43 at NNH_CorrectConfiguration.sdk)
  adapter             AspisV8R19.SqueezeOracleBridge.hashAdapter
  Oracle              CheckpointBytes5Inputs.Oracle at leadDigest (the
                      consumer of digestSource via native_binding/successful_call)
  program             ART_PartialProgram.program (the only place E_rec reads hashv
                      in ART_PartialAccount.wrapper)

Carrier laws are fields of `Carriers`; at the host each is an existing theorem:
  dec_enc      SqueezeOracleBridge.state_roundtrip
  enc_dec      SqueezeOracleBridge.array_roundtrip
  key_toB32    NNC_ByteCarriers.native_host (nativeKey (NNC_ResumeEvents.digest d) = d)
  flat_host    NNC_ByteCarriers.native_host under List.flatMap/List.map
-/
set_option autoImplicit false

namespace DGP

inductive Res (α : Type) where
  | ok : α → Res α
  | fail : Res α
  | div : Res α

def Res.bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, k => k a
  | .fail, _ => .fail
  | .div, _ => .div

structure Carriers where
  Parts : Type
  HostParts : Type
  Bytes : Type
  State : Type
  Digest : Type
  B32 : Type
  flatten : Parts → Bytes
  hostParts : Parts → HostParts
  hostFlatten : HostParts → Bytes
  enc : State → Digest
  dec : Digest → State
  nativeKey : B32 → Digest
  toB32 : Digest → B32
  dec_enc : ∀ s, dec (enc s) = s
  enc_dec : ∀ d, enc (dec d) = d
  key_toB32 : ∀ d, nativeKey (toB32 d) = d
  flat_host : ∀ p, hostFlatten (hostParts p) = flatten p

variable (C : Carriers)

/-- S2W_DigestExtraction.digest (self is the unit SolanaDigest). -/
def digest (hashv : C.Parts → Res C.Digest) (_self : Unit) (parts : C.Parts) : Res C.Digest :=
  (hashv parts).bind fun h => .ok h

theorem digest_eq_hashv (hashv : C.Parts → Res C.Digest) (self : Unit) (parts : C.Parts) :
    digest C hashv self parts = hashv parts := by
  unfold digest; cases hashv parts <;> rfl

def RuntimeSyscall (hashv : C.Parts → Res C.Digest) (sha256 : C.Bytes → C.State) : Prop :=
  ∀ parts d, hashv parts = .ok d → C.dec d = sha256 (C.flatten parts)

def P1 (sha256 H : C.Bytes → C.State) : Prop := ∀ b, sha256 b = H b

def DigestSource (op43 : Unit → C.Parts → Res C.Digest) (hashv : C.Parts → Res C.Digest) : Prop :=
  ∀ self parts, op43 self parts = digest C hashv self parts

/-- LIB_Env.hashv: total; reads the RSL env sha256 reply at the host partition. -/
def libHashv (env : C.HostParts → C.B32) (parts : C.Parts) : Res C.Digest :=
  .ok (C.nativeKey (env (C.hostParts parts)))

/-- SqueezeOracleBridge.hashAdapter. -/
def adapter (sha256 : C.Bytes → C.State) (parts : C.Parts) : Res C.Digest :=
  .ok (C.enc (sha256 (C.flatten parts)))

/-- The host env sha256 reply proposed for `NNH_HostEnv.Runtime.sha`. -/
def shaReply (sha256 : C.Bytes → C.State) : C.HostParts → C.B32 :=
  fun ps => C.toB32 (C.enc (sha256 (C.hostFlatten ps)))

/-- CheckpointBytes5Inputs.Oracle at the installed digest. -/
def Oracle (op43 : Unit → C.Parts → Res C.Digest) (H : C.Bytes → C.State) : Prop :=
  ∀ parts d, op43 () parts = .ok d → C.dec d = H (C.flatten parts)

/-! ## 0. The P2 counterexample (NNH_PreflightDigest), reproduced -/

def divergent : C.Parts → Res C.Digest := fun _ => .div

theorem divergent_runtime (sha256 : C.Bytes → C.State) :
    RuntimeSyscall C (divergent C) sha256 := by
  intro parts d h; cases h

theorem divergent_fails (env : C.HostParts → C.B32) (parts : C.Parts) :
    ¬ DigestSource C (fun _ => libHashv C env) (divergent C) := by
  intro h
  have := h () parts
  rw [digest_eq_hashv] at this
  cases this

/-! ## 1. Option (a): instantiate hashv := adapter sha256, env sha := shaReply sha256 -/

/-- The headline `syscall` binder at the instantiation: a theorem, no premise. -/
theorem syscall_adapter (sha256 : C.Bytes → C.State) :
    RuntimeSyscall C (adapter C sha256) sha256 := by
  intro parts d h
  cases h
  exact C.dec_enc _

/-- The literal op43 at the host env equals the instantiated hashv, pointwise. -/
theorem op43_eq_adapter (sha256 : C.Bytes → C.State) (parts : C.Parts) :
    libHashv C (shaReply C sha256) parts = adapter C sha256 parts := by
  unfold libHashv shaReply adapter
  rw [C.key_toB32, C.flat_host]

/-- A0 digestSource at the instantiation. -/
theorem digestSource_adapter (sha256 : C.Bytes → C.State) :
    DigestSource C (fun _ => libHashv C (shaReply C sha256)) (adapter C sha256) := by
  intro self parts
  rw [digest_eq_hashv]
  exact op43_eq_adapter C sha256 parts

/-- The instantiation is not an arbitrary choice: it is the ONLY total hashv
that the retained runtime row admits.  So instantiating it adds no content
beyond "the syscall model returns on every input", which on returning runs
(the only runs the top consumes) is the existing row itself. -/
theorem total_syscall_unique (hashv : C.Parts → Res C.Digest) (sha256 : C.Bytes → C.State)
    (total : ∀ p, ∃ d, hashv p = .ok d) (rt : RuntimeSyscall C hashv sha256) :
    ∀ p, hashv p = adapter C sha256 p := by
  intro p
  obtain ⟨d, hd⟩ := total p
  rw [hd]
  unfold adapter
  rw [← rt p d hd, C.enc_dec]

/-- Downstream consumer check: the instantiation delivers the headline Oracle
field at H whenever P1 holds (P1 is unchanged; with sha256 := H it is rfl). -/
theorem oracle_at_instantiation (sha256 H : C.Bytes → C.State) (p1 : P1 C sha256 H) :
    Oracle C (fun _ => libHashv C (shaReply C sha256)) H := by
  intro parts d h
  change libHashv C (shaReply C sha256) parts = .ok d at h
  rw [op43_eq_adapter] at h
  cases h
  rw [C.dec_enc]
  exact p1 _

/-- With sha256 := H (the per-world instantiation), P1 is definitional. -/
theorem p1_rfl (H : C.Bytes → C.State) : P1 C H H := fun _ => rfl

/-- Why the ExecB `Fixed` placement of hashv/sha256/p1/syscall cannot stand:
a world-independent hashv that satisfies the runtime row at two oracles that
differ at an input never returns there.  So under ANY resolution in which the
model digest returns, its values (and op43's) must vary with H, and the
averaging step needs the status lemma of section 4. -/
theorem fixed_hashv_never_returns (hashv : C.Parts → Res C.Digest) (s1 s2 : C.Bytes → C.State)
    (r1 : RuntimeSyscall C hashv s1) (r2 : RuntimeSyscall C hashv s2) (p : C.Parts)
    (differ : s1 (C.flatten p) ≠ s2 (C.flatten p)) : ∀ d, hashv p ≠ .ok d := by
  intro d h
  exact differ ((r1 p d h).symm.trans (r2 p d h))

/-! ## 2. Option (b): missing.op43 := hashv for the free binder -/

/-- digestSource then holds for EVERY hashv, by rfl through digest_eq_hashv... -/
theorem b_digestSource (hashv : C.Parts → Res C.Digest) :
    DigestSource C (fun _ => hashv) hashv := by
  intro self parts
  rw [digest_eq_hashv]

/-- ...but the model reply is then no longer the RSL returned digest, which A1/A2
need (ModelRet at the env reply).  The same divergent binder refutes it, so (b)
only relocates the P2 counterexample into A1/A2. -/
theorem b_relocates (sha256 : C.Bytes → C.State) (parts : C.Parts) :
    ¬ (∀ hashv, RuntimeSyscall C hashv sha256 →
        hashv parts = libHashv C (shaReply C sha256) parts) := by
  intro h
  have := h (divergent C) (divergent_runtime C sha256)
  cases this

/-! ## 3. Option (c): restrict digestSource to the returning branch -/

/-- (c1) "op43 returned d ⇒ hashv returned d": still refuted by the divergent binder. -/
def DigestSourceOk1 (op43 : Unit → C.Parts → Res C.Digest) (hashv : C.Parts → Res C.Digest) : Prop :=
  ∀ self parts d, op43 self parts = .ok d → hashv parts = .ok d

theorem c1_fails (env : C.HostParts → C.B32) (parts : C.Parts) :
    ¬ DigestSourceOk1 C (fun _ => libHashv C env) (divergent C) := by
  intro h
  have := h () parts _ rfl
  cases this

/-- (c2) "hashv returned d ⇒ op43 returned d": vacuous at the divergent binder. -/
def DigestSourceOk2 (op43 : Unit → C.Parts → Res C.Digest) (hashv : C.Parts → Res C.Digest) : Prop :=
  ∀ self parts d, hashv parts = .ok d → op43 self parts = .ok d

theorem c2_divergent (op43 : Unit → C.Parts → Res C.Digest) :
    DigestSourceOk2 C op43 (divergent C) := by
  intro self parts d h; cases h

/-! A concrete carrier showing (c2) + syscall + P1 do not deliver the Oracle
field the headline consumes, at the literal op43 with an env not tied to sha256. -/
def tiny : Carriers where
  Parts := Unit
  HostParts := Unit
  Bytes := Unit
  State := Nat
  Digest := Nat
  B32 := Nat
  flatten := fun _ => ()
  hostParts := fun _ => ()
  hostFlatten := fun _ => ()
  enc := id
  dec := id
  nativeKey := id
  toB32 := id
  dec_enc := fun _ => rfl
  enc_dec := fun _ => rfl
  key_toB32 := fun _ => rfl
  flat_host := fun _ => rfl

theorem c2_insufficient :
    DigestSourceOk2 tiny (fun _ => libHashv tiny (fun _ => (1 : Nat))) (divergent tiny) ∧
    RuntimeSyscall tiny (divergent tiny) (fun _ => (0 : Nat)) ∧
    P1 tiny (fun _ => (0 : Nat)) (fun _ => (0 : Nat)) ∧
    ¬ Oracle tiny (fun _ => libHashv tiny (fun _ => (1 : Nat))) (fun _ => (0 : Nat)) := by
  refine ⟨c2_divergent tiny _, divergent_runtime tiny _, fun _ => rfl, ?_⟩
  intro h
  have := h () (show Nat from 1) rfl
  exact Nat.succ_ne_zero 0 this

/-! ## 4. Averaging-side lemma: ART_PartialProgram reads only hashv's STATUS -/

/-- Oracle program (MemoizedProgramLaw.Program Bytes State, ask/done fragment). -/
inductive Prog (Bytes State R : Type) where
  | done : R → Prog Bytes State R
  | ask : Bytes → (State → Prog Bytes State R) → Prog Bytes State R

/-- CheckpointBytes5Effect.Code fragment used by ART_PartialProgram. -/
inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step : {B : Type} → Res B → (B → Code A) → Code A
  | read : C.Parts → (C.Digest → Code A) → Code A

structure Query where
  parts : C.Parts
  returned : Res C.Digest

/-- ART_PartialProgram.program, transcribed: the continuation receives
enc(oracle answer); hashv contributes only its constructor (ok/fail/div). -/
def program {A : Type} (hashv : C.Parts → Res C.Digest) :
    Code C A → List (Query C) → Prog C.Bytes C.State (Res A × List (Query C))
  | .done a, before => .done (.ok a, before)
  | .step r k, before => match r with
    | .ok a => program hashv (k a) before
    | .fail => .done (.fail, before)
    | .div => .done (.div, before)
  | .read parts k, before => .ask (C.flatten parts) fun value =>
    match hashv parts with
    | .ok _ => program hashv (k (C.enc value)) (before ++ [⟨parts, .ok (C.enc value)⟩])
    | .fail => .done (.fail, before ++ [⟨parts, .fail⟩])
    | .div => .done (.div, before ++ [⟨parts, .div⟩])

def SameStatus (h1 h2 : C.Parts → Res C.Digest) : Prop :=
  ∀ p, (∃ d1 d2, h1 p = .ok d1 ∧ h2 p = .ok d2) ∨ h1 p = h2 p

theorem program_status_congr {A : Type} (h1 h2 : C.Parts → Res C.Digest)
    (same : SameStatus C h1 h2) (code : Code C A) (before : List (Query C)) :
    program C h1 code before = program C h2 code before := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail => rfl
    | div => rfl
  | read parts k ih =>
    simp only [program]
    congr 1
    funext value
    rcases same parts with ⟨d1, d2, e1, e2⟩ | e
    · rw [e1, e2]; exact ih _ _
    · rw [e]
      cases h2 parts with
      | ok _ => exact ih _ _
      | fail => rfl
      | div => rfl

/-- The per-world instantiated hashv may be replaced, inside the account
program, by ONE world-independent total representative. -/
theorem program_adapter_fixed {A : Type} (sha256 : C.Bytes → C.State) (d0 : C.Digest)
    (code : Code C A) (before : List (Query C)) :
    program C (adapter C sha256) code before = program C (fun _ => .ok d0) code before :=
  program_status_congr C _ _ (fun _ => Or.inl ⟨_, _, rfl, rfl⟩) code before

end DGP

#print axioms DGP.divergent_fails
#print axioms DGP.syscall_adapter
#print axioms DGP.op43_eq_adapter
#print axioms DGP.digestSource_adapter
#print axioms DGP.total_syscall_unique
#print axioms DGP.oracle_at_instantiation
#print axioms DGP.p1_rfl
#print axioms DGP.fixed_hashv_never_returns
#print axioms DGP.b_digestSource
#print axioms DGP.b_relocates
#print axioms DGP.c1_fails
#print axioms DGP.c2_divergent
#print axioms DGP.c2_insufficient
#print axioms DGP.program_status_congr
#print axioms DGP.program_adapter_fixed
