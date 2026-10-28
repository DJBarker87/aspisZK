import R1Z.GamesR1
import R1Z.LazyFrozen

/-! Phase-indexed R1 games over the BINARY commitment trees (LOG D76; the
eight-way original is `R1Z.GamesR1P`, unchanged).  Only `NodeIdx` differs.

Phase-indexed R1 games (LOG D48.3, DESIGN-R1-REAL §1).

The landed `R1Prover.commit` returns all three roots before the transcript;
in Rust the C2 root depends on rows 0–1 (h1 = helper(λ, χ)) and the folded
root on rows ≤ 29 (fold(q, α0)).  Here the honest attempt is one CAUSAL READ
PROGRAM over `Pos1 = TRead ⊕ CPos`: the 115 transcript reads and the
commitment reads (three roots, the two expander streams, and `RIdx`: the two
binding reads, the three seed reads, the salts, leaves and non-root binary
nodes of the three trees), evaluated in the prover's order `ord` against the
oracle with partial answer vectors (`LazyFrozen.runC`).  Every address —
transcript or commitment — is computed from the answers read so far, so the
roots, the challenges `chOf W tr` and the tape are evaluated at the PARTIAL
vector; the C2 and folded roots therefore depend on the challenges before
them exactly as in Rust (R-causal, `RCausal`, makes this a fixpoint).

* `R1ProverP`: the commitment address map `caddr` (REF R-commit; its byte
  grammar is the named premise `RCommitBytes`, LayoutR1P), the leaf values,
  the mask decode `tapeOf` of the two expander streams (none = exhausted),
  the opened fibres, the verifier's opening list and the read order `ord`.
* `realGameP`: N attempts with independent secrets (nonce, field-mask
  entropy, leaf-salt seed, each a nonzero 32-byte value) against one oracle;
  the statement digest `H(public_bytes)` is read first; accept the first
  attempt with `P ∧ V ∧ ¬exhausted`; publish its view with the verifier log
  (115 transcript reads and the opening reads, answers `H(address)`), then
  the adversary's log; nothing of the other attempts.
* `fsR1P`: real = `realGameP`, ideal = the landed simulator game of `fsR1`;
  `abR1P = abR1` (the middle game and the ideal side are unchanged: the roots
  there are coins). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.GamesR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS
  R0Z.FsAbortBounds R1Z.Batched R1Z.ModelsVR1 R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1
  R1Z.LazyFrozen
attribute [local instance] Classical.propDecidable

/-! ### Commitment read index sets -/

/-- Fibres of one tree: `FIBRE_COUNT = 2^18` (aspis-core r0/mod.rs). -/
abbrev Fib := Fin (2 ^ 18)

/-- Non-root binary nodes (format adopted in LOG D76): level `d+1` (`d < 17`)
has `2^(17−d)` nodes; the root (level 18) is a separate position, so with the
three roots each tree has `2^18 − 1` parents (`CommitReadsR1.card_nodes`). -/
abbrev NodeIdx := Σ d : Fin 17, Fin (2 ^ (17 - d.val))

/-- The private commitment reads other than roots and expander blocks:
binding reads (0: precommit binding of prover.rs, 1: pool-v1 attempt binding),
seed reads (0: mask seed, 1: source-mask seed, 2: D seed), and per tree
(0: C1, 1: C2, 2: folded) the salts, leaves and non-root nodes. -/
abbrev RIdx := Fin 2 ⊕ Fin 3 ⊕ (Fin 3 × Fib) ⊕ (Fin 3 × Fib) ⊕ (Fin 3 × NodeIdx)

/-- Commitment positions: the three roots, the two expander streams, `RIdx`. -/
abbrev CPos (E₁ E₂ : ℕ) := Fin 3 ⊕ (Fin E₁ ⊕ Fin E₂) ⊕ RIdx

/-- All reads of one attempt. -/
abbrev Pos1 (E₁ E₂ : ℕ) := TRead ⊕ CPos E₁ E₂

/-- Count levels, not concrete nodes: the sum has only seventeen terms. -/
theorem card_NodeIdx : Fintype.card NodeIdx = 262142 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ (17 - i)) 17]
  norm_num [Finset.sum_range_succ]

/-- Includes both binding reads, which `CommitReadsR1.McR1` omits. -/
theorem card_Pos1 (E₁ E₂ : ℕ) :
    Fintype.card (Pos1 E₁ E₂) = 2359413 + E₁ + E₂ := by
  simp only [Pos1, CPos, RIdx, Fib, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, card_NodeIdx, card_TRead]
  norm_num <;> omega

/-- A nonzero 32-byte secret. -/
abbrev NZ := {v : OracleAnswer // v ≠ 0}

/-- Attempt secrets (StateOnlyAttemptSecrets): 0 the mask nonce, 1 the
field-mask entropy, 2 the leaf-salt seed.  None is published. -/
abbrev SecP := Fin 3 → NZ

instance : Nonempty NZ := ⟨⟨fun _ => 1, fun h => by
  have := congrFun h 0
  exact absurd this (by decide)⟩⟩

/-! ### The phase-indexed prover -/

structure R1ProverP (K CommitHandle Aux : Type) [Field K] (F : Subfield K)
    (W : R1Wire K CommitHandle Aux) where
  E₁ : ℕ
  E₂ : ℕ
  /-- commitment-read addresses (REF R-commit) from the instance, the
  statement, the attempt secrets, the statement digest, the mask tape, the
  `RIdx` answers and the challenges -/
  caddr : (h : HonestProver K) → h.Instance → Statement K CommitHandle → SecP → OracleAnswer →
    Tape K F → (RIdx → OracleAnswer) → Challenges K → CPos E₁ E₂ → List UInt8
  /-- the committed column values at fibre `u` of tree `T` -/
  leafVal : (h : HonestProver K) → h.Instance → Statement K CommitHandle → Tape K F →
    Challenges K → Fin 3 → Fib → List UInt8
  /-- the mask decode of the two expander streams (none: MaskSampleExhausted) -/
  tapeOf : (Fin E₁ → OracleAnswer) → (Fin E₂ → OracleAnswer) → Option (Tape K F)
  /-- the opened fibres of each tree (QueryScan; folded tree `u / 4`) -/
  openFib : Challenges K → Fin 3 → Finset Fib
  /-- the verifier's opening reads, in its order -/
  openList : Challenges K → List (Fin 3 ⊕ RIdx)
  /-- the prover's read order of one attempt -/
  ord : Fin (Fintype.card (Pos1 E₁ E₂)) ≃ Pos1 E₁ E₂

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

def tape0 : Tape K F := (0, 0)

section Attempt
variable {E₁ E₂ : ℕ}

def trOf (v : Pos1 E₁ E₂ → OracleAnswer) : TRead → OracleAnswer := fun j => v (.inl j)
def rootsOf (v : Pos1 E₁ E₂ → OracleAnswer) : Fin 3 → OracleAnswer := fun i => v (.inr (.inl i))
def e₁Of (v : Pos1 E₁ E₂ → OracleAnswer) : Fin E₁ → OracleAnswer :=
  fun c => v (.inr (.inr (.inl (.inl c))))
def e₂Of (v : Pos1 E₁ E₂ → OracleAnswer) : Fin E₂ → OracleAnswer :=
  fun c => v (.inr (.inr (.inl (.inr c))))
def restOf (v : Pos1 E₁ E₂ → OracleAnswer) : RIdx → OracleAnswer := fun q => v (.inr (.inr (.inr q)))

/-- An opening position as a commitment position. -/
def cposOf : Fin 3 ⊕ RIdx → CPos E₁ E₂
  | .inl i => .inl i
  | .inr q => .inr (.inr q)

end Attempt

section Game
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
include W Pr

/-- The mask tape decoded from an attempt's answers (default on exhaustion). -/
def tapeR (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : Tape K F :=
  (Pr.tapeOf (e₁Of v) (e₂Of v)).getD tape0

/-- The address of each read of one attempt, from its (partial) answer
vector `v`: transcript reads use the view at the challenges `chOf W (trOf v)`
and the roots `rootsOf v`; commitment reads use `caddr`. -/
def attAddr (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : Pos1 Pr.E₁ Pr.E₂ → List UInt8
  | .inl j => addr j (recP W x (view h B outputs x w (chOf W (trOf v)) (tapeR W Pr v)) (trOf v) (rootsOf v))
  | .inr c => Pr.caddr h w x sec d (tapeR W Pr v) (restOf v) (chOf W (trOf v)) c

abbrev n1 : ℕ := Fintype.card (Pos1 Pr.E₁ Pr.E₂)

/-- Attempt `k`'s answers inside the global answer vector. -/
def attVec {N : ℕ} (V : Fin (N * n1 W Pr) → OracleAnswer) (k : Fin N) :
    Pos1 Pr.E₁ Pr.E₂ → OracleAnswer :=
  fun p => V (finProdFinEquiv (k, Pr.ord.symm p))

/-- The global read program of `N` attempts (attempt-major, each in `ord`). -/
def gAddr (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) {N : ℕ} (sec : Fin N → SecP)
    (d : OracleAnswer) (g : Fin (N * n1 W Pr)) (V : Fin (N * n1 W Pr) → OracleAnswer) : List UInt8 :=
  attAddr W Pr h B outputs x w (sec (finProdFinEquiv.symm g).1) d
    (attVec W Pr V (finProdFinEquiv.symm g).1) (Pr.ord (finProdFinEquiv.symm g).2)

/-- One attempt's published data from its answers (verifier recomputation). -/
def attOut (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (H : List UInt8 → OracleAnswer) (sec : SecP)
    (d : OracleAnswer) (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : AttemptOut K CommitHandle Aux :=
  let ch := chOf W (trOf v)
  let τ := tapeR W Pr v
  let Vw := view h B outputs x w ch τ
  ⟨ch, Vw,
    schedule.map (fun j => (addr j (recP W x Vw (trOf v) (rootsOf v)),
      H (addr j (recP W x Vw (trOf v) (rootsOf v))))) ++
    (Pr.openList ch).map (fun c => (Pr.caddr h w x sec d τ (restOf v) ch (cposOf c),
      H (Pr.caddr h w x sec d τ (restOf v) ch (cposOf c)))),
    (Pr.tapeOf (e₁Of v) (e₂Of v)).isNone⟩

/-- The honest prover's attempts: the digest read, then the global read
program run in order against `H` (`runC`), then each attempt's output. -/
def realOut (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) {N : ℕ} (H : List UInt8 → OracleAnswer)
    (sec : Fin N → SecP) (k : Fin N) : AttemptOut K CommitHandle Aux :=
  attOut W Pr h B outputs x w H (sec k) (H (W.pubBytes x))
    (attVec W Pr (runC (gAddr W Pr h B outputs x w sec (H (W.pubBytes x))) H 0) k)

/-- The real game: accept the first attempt with `P ∧ V ∧ ¬ exhausted`. -/
def realGameP (N : ℕ) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (adv : R1Adv K CommitHandle Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (r : W.Tab × (Fin N → SecP)) :
    ROMView K CommitHandle Aux R1Bat :=
  let H := W.look r.1
  let out := realOut W Pr h B outputs x w H r.2
  match firstGood (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false) out with
  | none => ⟨W.failView, runLog (adv.prog W.failView []) H W.qmax⟩
  | some k => ⟨(out k).view, (out k).log ++ runLog (adv.prog (out k).view (out k).log) H W.qmax⟩

def fsR1P (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    FSExperiments K CommitHandle Aux R1Bat F where
  Adversary := R1Adv K CommitHandle Aux
  RealRand := W.Tab × (Fin N → SecP)
  IdealRand := (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)
  real := fun h B outputs adv x w r => realGameP W Pr N P Vp h B outputs adv x w r
  ideal := fun sim adv x r =>
    retryOut N (fun c => P (drawW W c)) (fun c t => sim (drawW W c) t)
      (fun c k v => (abR1 W N hN).extend adv x c k v) (fun c => (abR1 W N hN).fail adv x c) r
  observe := fun adv rv => adv.decide rv

instance instRealFinP (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Fintype (fsR1P (F := F) W Pr N hN P Vp).RealRand :=
  inferInstanceAs (Fintype (W.Tab × (Fin N → SecP)))

instance instRealNeP (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Nonempty (fsR1P (F := F) W Pr N hN P Vp).RealRand :=
  inferInstanceAs (Nonempty (W.Tab × (Fin N → SecP)))

instance instIdealFinP (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Fintype (fsR1P (F := F) W Pr N hN P Vp).IdealRand :=
  inferInstanceAs (Fintype ((Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)))

instance instIdealNeP (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Nonempty (fsR1P (F := F) W Pr N hN P Vp).IdealRand := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  exact inferInstanceAs (Nonempty ((Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)))

/-- The abort bridge of the phase-indexed games is the landed `abR1`. -/
abbrev abR1P (N : ℕ) (hN : 0 < N) := abR1 W N hN

end Game

#print axioms attAddr
#print axioms gAddr
#print axioms attOut
#print axioms realOut
#print axioms realGameP
#print axioms fsR1P
#print axioms card_NodeIdx
#print axioms card_Pos1
end R1Z.GamesR1PBin
