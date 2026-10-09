import R0Z.HonestView
import R0Z.StatisticalDistance
import R0P.SemD3Glue

/-! Historical Z1 interface retained under `Z1`, including the unchanged
FS/ROM distinguishing experiment. It is not the current privacy statement.

Z1: open privacy obligations for the 31-round interactive R0 model.

This file supplies data interfaces and goals, not an honest prover, simulator,
mask-image premise, error budget, or FS compiler theorem. `SourceData` is the
same interface used by SemD3Glue.sourceData; its paymentWitness is reused
literally. See ../../LOG.md for the source/public-view audit and lead decisions.

The reference interaction is total: 31 message/challenge rows, then a final
message. Failure (including q22's empty set) is retained in public outputs.
A source caller that stops before completing these rows needs an explicit
partial-transcript refinement; this file does not condition it on success.
-/
set_option autoImplicit false
namespace R0Z.ZkStatement.Z1
noncomputable section

abbrev Bytes := List UInt8
abbrev Round := Fin 31
abbrev ChallengePrefix (C : Type) (i : Round) := Fin i.val → C
abbrev Rows (M C : Type) (n : Nat) := Fin n → M × C

inductive Outcome
  | success
  | abort

/-- Explicit allowed outputs from Phase 0. Bytes are uninstantiated encodings,
not assertions that any two historical/current formats coincide. Events retain
all actually visible lifecycle/retry information, including visible counts. -/
structure PublicOutputs where
  statementBytes : Bytes
  afterstate : Bytes
  profile : Bytes
  release : Bytes
  descriptor : Bytes
  accountEnvelope : Bytes
  payerAndAccounts : List Bytes
  outputCommitments : List Bytes
  nullifiers : List Bytes
  commitmentRoots : List Bytes
  attemptIdentifier : Bytes
  researchNonces : List Bytes
  proofBytes : Bytes
  openingRecords : List Bytes
  sharedLeafSalts : List Bytes
  authenticationFrontiers : List Bytes
  serializedLengths : List Nat
  lifecycleEvents : List Bytes
  visibleAttemptCount : Option Nat
  outcome : Outcome

/-- Every model message and public challenge, including the terminal message.
`Statement` is TypedContext in the R0 instance: full words are not hidden by
replacing them with roots. The public byte projection is an additional field. -/
structure PublicView (Statement M C : Type) where
  statement : Statement
  rounds : Rows M C 31
  finalMessage : M
  outputs : PublicOutputs

/-- No laws/proofs in the honest-prover interface. Per-round messages have
access only to challenges strictly before that round. Salts/seeds/retry tapes
are represented by `rand`; their concrete distribution is not chosen here. -/
structure HonestProver (Statement M C : Type) where
  witness : Type
  rand : Type
  messages : Statement → witness → rand → (i : Round) → ChallengePrefix C i → M
  finish : Statement → witness → rand → Rows M C 31 → M × PublicOutputs
  valid : Statement → witness → Prop

/-- Finite-tape presentation of the model's sampler operations. `Internal`
can retain duplex state while `project` exposes the challenge value. `draw`
is data; its correspondence to the actual samplers is a GOAL in HVZK.
No uniform-field, freshness, successful-sampling, or FS law is assumed. -/
structure ModelSamplers (Statement M C Internal I A Coins : Type) where
  samp : Nat → FS.Prefix Statement M Internal → M → FS2.Sampler I A Internal
  draw : Round → FS.Prefix Statement M Internal → M → Coins → Internal
  project : Internal → C

variable {X M C Internal I A Coins : Type}

/-- Equality with the model's fresh-answer sampler law at every prefix.
The read trace is discarded; the internal challenge/state output is retained.
This is interactive sampling, not a shared memoized random-oracle execution. -/
def SamplerLaw [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    [Fintype Coins] [Nonempty Coins]
    (v : ModelSamplers X M C Internal I A Coins) : Prop :=
  ∀ (i : Round) (p : FS.Prefix X M Internal) (m : M) (test : Internal → ℚ),
    R0Z.mean (fun r => test (v.draw i p m r)) =
      AspisV8R19.AdaptiveFirstReadLaw.independentMean (v.samp i.val p m).toProgram
        (fun result => test result.2)

/-- A fresh verifier tape for each of the 31 rounds. -/
abbrev VerifierTape (Coins : Type) := Round → Coins

/-- Structural recursion on round count only; never on rows, states or traces.
The prover cannot inspect the current/future verifier tape. -/
def honestRows (h : HonestProver X M C)
    (v : ModelSamplers X M C Internal I A Coins)
    (x : X) (w : h.witness) (r : h.rand) (tape : VerifierTape Coins) :
    (n : Nat) → n ≤ 31 → Rows M Internal n
  | 0, _ => Fin.elim0
  | n + 1, hn =>
    let prev := honestRows h v x w r tape n (by omega)
    let i : Round := ⟨n, by omega⟩
    let m := h.messages x w r i (fun j => v.project (prev j).2)
    let c := v.draw i ⟨x, List.ofFn prev⟩ m (tape i)
    Fin.snoc prev (m, c)

/-- Honest view as a function of prover coins and independent verifier coins.
There is no success filter, and the statement (including W) is retained. -/
def honestView (h : HonestProver X M C)
    (v : ModelSamplers X M C Internal I A Coins)
    (x : X) (w : h.witness) (tape : h.rand × VerifierTape Coins) : PublicView X M C :=
  let rs := honestRows h v x w tape.1 tape.2 31 (Nat.le_refl 31)
  let publicRows : Rows M C 31 := fun i => ((rs i).1, v.project (rs i).2)
  let final := h.finish x w tape.1 publicRows
  ⟨x, publicRows, final.1, final.2⟩

/-- Offline honest-verifier simulator. It receives the public statement and
finite tapes, never a witness. No efficiency or ROM-programming claim is made. -/
structure Simulator (Statement M C Coins : Type) where
  simRand : Type
  simulate : Statement → simRand → VerifierTape Coins → PublicView Statement M C

/-- Open HVZK target. Alignment and sampler-law equalities are goals, never
premises smuggled into a security theorem. For the source instance, `valid`
MUST equal sourceData.paymentWitness. Epsilon is symbolic; equality in law can
later discharge the distance goal via dist_zero_of_equalLaws. -/
def HVZK (h : HonestProver X M C) (paymentWitness : X → h.witness → Prop)
    (v : ModelSamplers X M C Internal I A Coins) (sim : Simulator X M C Coins)
    [Fintype h.rand] [Nonempty h.rand] [Fintype sim.simRand] [Nonempty sim.simRand]
    [Fintype Coins] [Nonempty Coins] [DecidableEq I] [Inhabited A]
    [Fintype A] [Nonempty A] (epsilon_zk : ℚ) : Prop :=
  h.valid = paymentWitness ∧ SamplerLaw v ∧
    ∀ (x : X) (w : h.witness), paymentWitness x w →
      R0Z.dist (honestView h v x w)
        (fun tape : sim.simRand × VerifierTape Coins => sim.simulate x tape.1 tape.2)
        ≤ epsilon_zk

/-- FS/ROM observer view adds only the observer's own queries and full 256-bit
answers, not the honest prover's private hash-input log. -/
structure ROMView (Statement M C : Type) where
  publicView : PublicView Statement M C
  observerOracle : List (Bytes × (Fin 32 → UInt8))

/-- Future FS/ROM experiment/compiler operations, all data. The adversary class,
query caps, encodings, memoization/programming policy and concrete compiler are
lead decisions. Both sides receive the SAME honest prover / simulator objects
used by HVZK. No compiler correctness or computational assumption is a field. -/
structure FSExperiments (Statement M C Coins : Type) where
  adversary : Type
  realRand : Type
  idealRand : Type
  real : (h : HonestProver Statement M C) → adversary → Statement →
    h.witness → realRand → ROMView Statement M C
  ideal : Simulator Statement M C Coins → adversary → Statement →
    idealRand → ROMView Statement M C
  observe : adversary → ROMView Statement M C → Bool

/-- Separate, unproved FS/ROM distinguishing-advantage target. No implication
from interactive HVZK is asserted; the exact games/adversary class remain data.
In particular this does not select a seed assumption or a query budget. -/
def ZK_FS (h : HonestProver X M C) (paymentWitness : X → h.witness → Prop)
    (sim : Simulator X M C Coins) (fs : FSExperiments X M C Coins)
    [Fintype fs.realRand] [Nonempty fs.realRand]
    [Fintype fs.idealRand] [Nonempty fs.idealRand] (epsilon_fs : ℚ) : Prop :=
  ∀ (adv : fs.adversary) (x : X) (w : h.witness), paymentWitness x w →
    |R0Z.mean (fun r => if fs.observe adv (fs.real h adv x w r) then 1 else 0) -
      R0Z.mean (fun r => if fs.observe adv (fs.ideal sim adv x r) then 1 else 0)|
      ≤ epsilon_fs

/-! Exact R0 type aliases; no clone of TypedContext, SemMsg, Msg or Chal. -/
abbrev Statement (K : Type) [Field K] (Sfield : Fin 29 → Subfield K) :=
  R0P.SemSource.TypedContext K Sfield
abbrev Msg (K : Type) [Field K] := R0C.SemStatement.Msg K K (R0P.SemSource.SemMsg K)
abbrev Chal (K : Type) [Field K] := R0C.SemStatement.Chal K K

/-- Like SemStatement.Obligations: only operations/data and structural typeclass
instances are parameters. There is no assumed privacy, sampler law, mask-image
condition or computational assumption. Passing SemD3Glue.sourceData (or its
field-generic sourceDataWithFallback) reuses its paymentWitness literally. -/
def Obligations {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}
    (h : HonestProver (Statement K Sfield) (Msg K) (Chal K))
    (s : R0C.SemStatement.SourceData (K := K) (E := K)
      (Statement K Sfield) (R0P.SemSource.SemMsg K) h.witness Sfield)
    (v : ModelSamplers (Statement K Sfield) (Msg K) (Chal K) Internal I A Coins)
    (sim : Simulator (Statement K Sfield) (Msg K) (Chal K) Coins)
    (fs : FSExperiments (Statement K Sfield) (Msg K) (Chal K) Coins)
    [Fintype h.rand] [Nonempty h.rand] [Fintype sim.simRand] [Nonempty sim.simRand]
    [Fintype Coins] [Nonempty Coins] [DecidableEq I] [Inhabited A]
    [Fintype A] [Nonempty A] [Fintype fs.realRand] [Nonempty fs.realRand]
    [Fintype fs.idealRand] [Nonempty fs.idealRand]
    (epsilon_zk epsilon_fs : ℚ) : Prop :=
  HVZK h s.paymentWitness v sim epsilon_zk ∧ ZK_FS h s.paymentWitness sim fs epsilon_fs

/-- Honest operations separated from their relation: this constructor installs
sourceData.paymentWitness directly, rather than asking for it as a premise. -/
structure ProverOperations (Statement M C W R : Type) where
  messages : Statement → W → R → (i : Round) → ChallengePrefix C i → M
  finish : Statement → W → R → Rows M C 31 → M × PublicOutputs

abbrev proverForSource {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}
    {W R : Type}
    (s : R0C.SemStatement.SourceData (K := K) (E := K)
      (Statement K Sfield) (R0P.SemSource.SemMsg K) W Sfield)
    (ops : ProverOperations (Statement K Sfield) (Msg K) (Chal K) W R) :
    HonestProver (Statement K Sfield) (Msg K) (Chal K) where
  witness := W
  rand := R
  messages := ops.messages
  finish := ops.finish
  valid := s.paymentWitness

open R0P.SemD3Glue AspisV8R19.SourceDuplexStep

/-- The actual combined sampler, with only a finite-tape realizer left open.
No replacement protocol or independently uniform field challenge is installed.
Its retained duplex state is internal; every challenge value is public. -/
def combinedSamplers {Sfield : Fin 29 → Subfield SemE} {L : Nat}
    (p : FS2.Duplex.Params (Msg SemE) (Chal SemE) L)
    (draw : Round → FS.Prefix (Statement SemE Sfield) (Msg SemE)
      (FS2.Duplex.Chal (Chal SemE)) → Msg SemE → Coins → FS2.Duplex.Chal (Chal SemE)) :
    ModelSamplers (Statement SemE Sfield) (Msg SemE) (Chal SemE)
      (FS2.Duplex.Chal (Chal SemE)) (FS2.Duplex.Addr L) State Coins where
  samp := combinedSampler p
  draw := draw
  project := Prod.fst

/-- Concrete connection to the same reference model as combinedProtocol.
The field-generic Obligations above remains available. Here witness = Trace,
valid = sourceData.paymentWitness and samp = combinedProtocol.samp by definition.
The encoding/decoder parameters p are precisely the soundness model's data;
freezing its concrete decoder identities is not a privacy assumption. -/
def R0Obligations {Sfield : Fin 29 → Subfield SemE} {L : Nat} {R : Type}
    (B : R0P.PackBasis (Sfield 0))
    (p : FS2.Duplex.Params (Msg SemE) (Chal SemE) L)
    (ops : ProverOperations (Statement SemE Sfield) (Msg SemE) (Chal SemE) (R0P.Trace SemE) R)
    (draw : Round → FS.Prefix (Statement SemE Sfield) (Msg SemE)
      (FS2.Duplex.Chal (Chal SemE)) → Msg SemE → Coins → FS2.Duplex.Chal (Chal SemE))
    (sim : Simulator (Statement SemE Sfield) (Msg SemE) (Chal SemE) Coins)
    (fs : FSExperiments (Statement SemE Sfield) (Msg SemE) (Chal SemE) Coins)
    [Fintype R] [Nonempty R] [Fintype Coins] [Nonempty Coins]
    [Fintype sim.simRand] [Nonempty sim.simRand]
    [Fintype fs.realRand] [Nonempty fs.realRand]
    [Fintype fs.idealRand] [Nonempty fs.idealRand]
    (epsilon_zk epsilon_fs : ℚ) : Prop :=
  Obligations (proverForSource (sourceData B) ops) (sourceData B)
    (combinedSamplers p draw) sim fs epsilon_zk epsilon_fs

#print axioms ProverOperations
#print axioms proverForSource
#print axioms combinedSamplers
#print axioms R0Obligations

#print axioms PublicOutputs
#print axioms PublicView
#print axioms HonestProver
#print axioms ModelSamplers
#print axioms SamplerLaw
#print axioms honestRows
#print axioms honestView
#print axioms Simulator
#print axioms HVZK
#print axioms ROMView
#print axioms FSExperiments
#print axioms ZK_FS
#print axioms Statement
#print axioms Msg
#print axioms Chal
#print axioms Obligations
end
end R0Z.ZkStatement.Z1

/-! Current D1/D2/D4′/D4″/D9 interactive statement. -/
namespace R0Z.ZkStatement
noncomputable section
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView Polynomial
open AspisWide.InitialEncoder AspisWide.Agreement AspisPool.AlgorithmicCircleDecoderV7
attribute [local instance] Classical.propDecidable

abbrev Statement (K CommitHandle : Type) := Public K × CommitHandle
abbrev Challenges (K : Type) [Field K] := HonestView.Challenges K
abbrev Payload (K : Type) := HonestView.Payload K

/-- The transfer-instance builder is deliberately uninstantiated. No relation,
affinity, mask-image, privacy or completeness fact is a structure field. -/
structure HonestProver (K : Type) where
  Instance : Type
  «public» : Instance → Public K
  build : Instance → Trace K

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

abbrev HonestInstance (h : HonestProver K) (F : Subfield K) :=
  h.Instance × EligibleNoise K F

def «public» (h : HonestProver K) (w : HonestInstance h F) : Public K := h.public w.1

def build (h : HonestProver K) (w : HonestInstance h F) : Trace K :=
  applyEligible (h.build w.1) w.2

/-- Handles are nominal names derived from the public commitment namespace.
All auxiliary outputs/encodings are public data, parameterised only by x,ch.
Their source byte/account refinement is D7, outside this interactive model. -/
structure Meta (K CommitHandle Aux : Type) [Field K] where
  statement : Statement K CommitHandle
  challenges : Challenges K
  handles : Fin 2 → CommitHandle × Fin 2
  publicOutputs : Aux

abbrev View (K CommitHandle Aux : Type) [Field K] := Meta K CommitHandle Aux × Payload K

/-- The type itself excludes any dependency on instance, eligible noise or tape. -/
def metadata (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (ch : Challenges K) : Meta K CommitHandle Aux :=
  ⟨x, ch, fun i => (x.2, i), outputs x ch⟩

def payload (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : HonestInstance h F) (ch : Challenges K) : AffTape K F → Payload K :=
  HonestView.run x.1 B (build h w) ch

def view (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h F) (ch : Challenges K)
    (r : AffTape K F) : View K CommitHandle Aux :=
  (metadata outputs x ch, payload h B x w ch r)

/-- A and b are payload-valued: Meta has no fictitious vector-space instance. -/
def A (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : HonestInstance h F) (ch : Challenges K) : AffTape K F →ₗ[F] Payload K :=
  (payloadAffine x.1 B (build h w) ch).linear

def b (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : HonestInstance h F) (ch : Challenges K) : Payload K := payload h B x w ch 0

theorem payload_affine (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : HonestInstance h F) (ch : Challenges K)
    (r : AffTape K F) : payload h B x w ch r = b h B x w ch + A h B x w ch r := by
  simp only [payload, b, A, HonestView.run_eq_payloadAffine]
  have he := congrFun (AffineMap.decomp (payloadAffine x.1 B (build h w) ch)) r
  exact he.trans (add_comm _ _)

/-- Actual trace affinity is established by MaskLayout, and the only nonlinear
semantic operation in the fixed instance is split by ViewAffine.originalAt_affine.
All later evaluations, sums, interpolation, encoding and opening maps are linear. -/
theorem view_affine (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h F) (ch : Challenges K)
    (r : AffTape K F) : view h B outputs x w ch r =
      (metadata outputs x ch, b h B x w ch + A h B x w ch r) := by
  exact congrArg (fun p => (metadata outputs x ch, p)) (payload_affine h B x w ch r)

/-- D4′ verbatim on payloads, over the augmented instance (w,e). The public
comparison uses x.1 because x.2 is the ideal public handle namespace. -/
def MaskImage (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  ∀ w w' ch, «public» h w = x.1 → «public» h w' = x.1 →
    LinearMap.range (A h B x w ch) = LinearMap.range (A h B x w' ch) ∧
    b h B x w ch - b h B x w' ch ∈ LinearMap.range (A h B x w ch)

def InLanguage (h : HonestProver K) (x : Statement K CommitHandle) : Prop :=
  ∃ w : HonestInstance h F, «public» h w = x.1

/-- Classical choice is used only for a statement in the language. Outside it
all privacy quantifiers are vacuous; no default witness is assumed. -/
def simulator (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hx : InLanguage (F := F) h x) (ch : Challenges K) :
    AffTape K F → View K CommitHandle Aux :=
  view h B outputs x (Classical.choose hx) ch

/-- The real ideal-tape experiment includes independent eligible noise. -/
def honestLawRun (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K)
    (tape : EligibleNoise K F × AffTape K F) : View K CommitHandle Aux :=
  view h B outputs x (w, tape.1) ch tape.2

def HVZK_conditional (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop :=
  ∀ (hx : InLanguage (F := F) h x) w ch, «public» h w = x.1 →
    EqualLaws (view h B outputs x w ch) (simulator h B outputs x hx ch)

/-- D8, epsilon = 0: equality of laws of the complete (metadata,payload) pair.
Challenges are fixed first and universally quantified, not conditioned good. -/
def HVZK_perfect (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop :=
  ∀ (hx : InLanguage (F := F) h x) (w : h.Instance) ch, h.public w = x.1 →
    EqualLaws (honestLawRun h B outputs x w ch) (simulator h B outputs x hx ch)

/-- General distance notation is retained; the target used here is exactly 0. -/
def HVZK (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (epsilon : ℚ) : Prop :=
  ∀ (hx : InLanguage (F := F) h x) (w : h.Instance) ch, h.public w = x.1 →
    dist (honestLawRun h B outputs x w ch) (simulator h B outputs x hx ch) ≤ epsilon

/-- D2's relation is literally sourceData.paymentWitness (SemD3Glue:98,111).
This is an obligation on the uninstantiated builder, not a witness premise. -/
def Completeness (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  ∀ (w : HonestInstance h F) ch r, «public» h w = x.1 →
    InputNoteExtracted x.1 (applyAff B (prepare x.1 (build h w) ch) r)

def Obligations (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  MaskImage h B x ∧ Completeness h B x

/-- Word-valued outputs belong to the prover; View has no trace or whole word. -/
structure ProverOutput (K CommitHandle Aux : Type) [Field K] where
  W : Fin 29 → InitialWord K
  C2 : Fin 2 → InitialWord K
  disclosed : View K CommitHandle Aux

def proverOutput (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h F) (ch : Challenges K)
    (r : AffTape K F) : ProverOutput K CommitHandle Aux :=
  let t := applyAff B (prepare x.1 (build h w) ch) r
  ⟨fun c => if c.val = 26 ∨ c.val = 27 then 0 else exactInitialEncoder (t c),
    fun j => exactInitialEncoder (t (if j.val = 0 then 26 else 27)),
    view h B outputs x w ch r⟩

inductive IdealSemMsg (K CommitHandle : Type) [Field K]
  | none
  | c2 (handle : CommitHandle × Fin 2)
  | maskSum (s : K)
  | roundPoly (p : K[X])

abbrev Msg (K CommitHandle : Type) [Field K] :=
  R0C.SemStatement.Msg K K (IdealSemMsg K CommitHandle)
abbrev Chal (K : Type) [Field K] := MaskedProtocol.Chal K

def coefficientPolynomial {n : Nat} (p : Fin n → K) : K[X] :=
  ∑ i : Fin n, monomial i.val (p i)

/-- The actual 32-row schedule, with only the ideal C2 word-to-handle projection
changed from the soundness outer message tags. Repeated disclosures use the
same payload coordinates; query openings are the final response projection. -/
def messages (x : Statement K CommitHandle) (p : Payload K) (i : Fin 32) : Msg K CommitHandle :=
  match MaskedProtocol.schedule i with
  | .lambda | .chi | .zerocheck _ | .mu => .semantic .none
  | .c2Theta => .semantic (.c2 (x.2, 1))
  | .maskSumEta => .semantic (.maskSum (p .maskSum))
  | .sumcheck j => .semantic (.roundPoly (coefficientPolynomial (fun k => p (.semanticCoeff j k))))
  | .circle j => if j.val = 0 then .beforeZ0 (fun j c => p (.pointClaim j c))
      else .beforeZ1 (fun c => p (.ood 0 c))
  | .opening j => if j.val = 0 then .opening (.values (fun c z => p (.ood z c)))
      else if j.val = 1 then .opening (.scalar (p .inactiveSum))
      else if j.val = 2 then .opening .unit
      else if j.val = 3 then .opening (.poly (coefficientPolynomial (fun k => p (.openingCoeff k))))
      else .opening (.final (fun k => p (.finalCoeff k)))

def honestMessages (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : HonestInstance h F) (ch : Challenges K)
    (r : AffTape K F) (i : Fin 32) : Msg K CommitHandle :=
  messages x (payload h B x w ch r) i

/-- The nullary opening tag is accompanied by exactly the query-gated symbols
in Payload.opened; it never includes the rest of the committed words. -/
def finalMessage : Msg K CommitHandle := .opening .opening

def challengeAt (ch : Challenges K) (i : Fin 32) : Chal K :=
  if h : i.val < 25 then .semantic (ch.sem ⟨i.val, h⟩)
  else if h : i.val < 27 then .circle (ch.circle ⟨i.val-25, by omega⟩)
  else if h : i.val < 31 then .opening (.field (ch.opening ⟨i.val-27, by omega⟩))
  else .opening (.set ch.queries)

#print axioms view_affine
#print axioms MaskImage
#print axioms HVZK_perfect
#print axioms Completeness
#print axioms Obligations
#print axioms proverOutput
#print axioms messages
end
end R0Z.ZkStatement
