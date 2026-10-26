import R0Z.HvzkS
import R1Z.ModelsVR1
import R1Z.TranscriptR1

/-! R1 games (zf1/DESIGN-R1-GAMES §3–§6).  Concrete `FSExperiments` and
`AbortBridge` for the retrying R1 prover, over the 115-read transcript layout
of `TranscriptR1`, and the R1 models discharged from them.

* Attempt coins `R1Coins`: every transcript read's answer, the three
  commitment roots (C1, C2, folded), the commitment answers `Cm` (salts,
  leaves, nodes; abstract) and the shared table `Tab`.
* `abR1`: `draw` decodes the 40 squeeze answers; `extend` publishes the view
  together with the VERIFIER LOG (the 115 transcript reads and the
  commitment-opening reads, G-root) and runs the adversary against the
  table programmed at the published addresses; `fail` publishes nothing.
* `fsR1.real`: the honest prover retries up to `N` attempts with fresh
  secrets and accepts on `P ∧ V ∧ ¬ exhausted`; the transcript is computed
  adaptively against the oracle `look tab`.
* `fsR1.ideal`: the same loop on `P` with the simulator's view and the
  middle game's programmed table (witness-free given the simulator).

PROVED: `idealModel_R1` (every field of `R1IdealModelV`: identity coupling,
agreement, freshness), and `realModel_R1`: `R1RealModelV` with
`M = N · (115 + Mc)` positions, where the transcript `HitFresh` /
`PairFresh` facts and the transcript–commitment cross pairs are theorems,
from `R1RealData`: the coupling with a coordinate-projection `toM` (G-prog),
agreement outside the events (G-ref), the commitment-read layout
(`CmLayout`, H-layout for salts/leaves/nodes) and the exhaustion mass. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.GamesR1
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS
  R0Z.FsAbortBounds R1Z.Batched R1Z.ModelsVR1 R1Z.LensR1 R1Z.TranscriptR1
attribute [local instance] Classical.propDecidable

/-! ### Adversaries: adaptive oracle programs -/

inductive OProg
  | done
  | query (a : List UInt8) (k : OracleAnswer → OProg)

/-- The adversary's query/answer log against oracle `O`, at most `n` reads. -/
def runLog : OProg → (List UInt8 → OracleAnswer) → ℕ → List (List UInt8 × OracleAnswer)
  | .done, _, _ => []
  | .query _ _, _, 0 => []
  | .query a k, O, n + 1 => (a, O a) :: runLog (k (O a)) O n

/-- A post-proof adversary: a query program on the published data and a
decision on its whole view (published data and its own log). -/
structure R1Adv (K CommitHandle Aux : Type) [Field K] where
  prog : View K CommitHandle Aux R1Bat → List (List UInt8 × OracleAnswer) → OProg
  decide : ROMView K CommitHandle Aux R1Bat → Bool

/-! ### Attempt coins and the wire data -/

/-- Transcript answers, roots (C1, C2, folded), commitment answers, table. -/
abbrev R1Coins (Cm Tab : Type) :=
  (TRead → OracleAnswer) × (Fin 3 → OracleAnswer) × Cm × Tab

/-- The R1 wire data (REF: r1_wire.rs / verifier.rs / sampler.rs). -/
structure R1Wire (K CommitHandle Aux : Type) [Field K] where
  Cm : Type
  finCm : Fintype Cm
  neCm : Nonempty Cm
  Tab : Type
  finTab : Fintype Tab
  neTab : Nonempty Tab
  /-- the shared table read as an oracle -/
  look : Tab → List UInt8 → OracleAnswer
  /-- framed records of rows 0..26; row 2 carries the C2 root -/
  frame : View K CommitHandle Aux R1Bat → OracleAnswer → Fin 27 → List UInt8
  /-- payloads of rows 27..30; row 30 carries the folded root -/
  payload : View K CommitHandle Aux R1Bat → OracleAnswer → Fin 4 → List UInt8
  /-- row 31's final message -/
  final : View K CommitHandle Aux R1Bat → List UInt8
  pubBytes : Statement K CommitHandle → List UInt8
  vtag : UInt8
  /-- the decoders of the 27 semantic, 4 opening, 8 query and the ρ blocks -/
  dec : (Fin 27 → OracleAnswer) → (Fin 4 → OracleAnswer) → (Fin 8 → OracleAnswer) →
    OracleAnswer → Challenges K
  /-- the QueryScan completion index -/
  kstarOf : (Fin 8 → OracleAnswer) → Fin 8
  /-- the verifier's reads on the opened paths (leaves with opened salts, nodes) -/
  comLog : Cm → (Fin 3 → OracleAnswer) → View K CommitHandle Aux R1Bat → Challenges K →
    List (List UInt8 × OracleAnswer)
  failView : View K CommitHandle Aux R1Bat
  qmax : ℕ

attribute [instance] R1Wire.finCm R1Wire.neCm R1Wire.finTab R1Wire.neTab

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

section Wire
variable (W : R1Wire K CommitHandle Aux)

def chOf (tr : TRead → OracleAnswer) : Challenges K :=
  W.dec (fun i => tr (.sqS i)) (fun i => tr (.sqO i)) (fun k => tr (.qb k)) (tr .sqR)

def drawW (c : R1Coins W.Cm W.Tab) : Challenges K := chOf W c.1

/-- The record of an attempt whose published view is `V`. -/
def recP (x : Statement K CommitHandle) (V : View K CommitHandle Aux R1Bat)
    (tr : TRead → OracleAnswer) (roots : Fin 3 → OracleAnswer) : Rec :=
  ⟨tr, roots 0, W.kstarOf (fun k => tr (.qb k)),
    ⟨W.frame V (roots 1), W.payload V (roots 2), W.final V, W.pubBytes x, W.vtag⟩⟩

/-- The verifier's transcript reads, in schedule order. -/
def tLog (x : Statement K CommitHandle) (V : View K CommitHandle Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) : List (List UInt8 × OracleAnswer) :=
  TranscriptR1.schedule.map (fun j => (addr j (recP W x V c.1 c.2.1), c.1 j))

/-- The verifier log (G-root): transcript reads, then the opening reads. -/
def verLog (x : Statement K CommitHandle) (V : View K CommitHandle Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) : List (List UInt8 × OracleAnswer) :=
  tLog W x V c ++ W.comLog c.2.2.1 c.2.1 V (drawW W c)

/-- The table programmed at the published addresses. -/
def progOracle (x : Statement K CommitHandle) (V : View K CommitHandle Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab) : List UInt8 → OracleAnswer := fun a =>
  match List.lookup a (verLog W x V c) with
  | some v => v
  | none => W.look tab a

/-- The R1 abort bridge; the shared table is attempt 0's table coordinate. -/
def abR1 (N : ℕ) (hN : 0 < N) : AbortBridge K CommitHandle Aux R1Bat (R1Adv K CommitHandle Aux) where
  Coins := R1Coins W.Cm W.Tab
  finiteCoins := inferInstance
  nonemptyCoins := inferInstance
  N := N
  draw := fun _ _ c => drawW W c
  extend := fun adv x c k V =>
    ⟨V, verLog W x V (c k) ++
      runLog (adv.prog V (verLog W x V (c k))) (progOracle W x V (c k) (c ⟨0, hN⟩).2.2.2) W.qmax⟩
  fail := fun adv _ c =>
    ⟨W.failView, runLog (adv.prog W.failView []) (W.look (c ⟨0, hN⟩).2.2.2) W.qmax⟩

end Wire

/-! ### The generic retry output -/

def retryOut {C T V O : Type} (N : ℕ) (Pd : C → Prop) (pub : C → T → V)
    (ext : (Fin N → C) → Fin N → V → O) (fail : (Fin N → C) → O)
    (ct : (Fin N → C) × (Fin N → T)) : O :=
  match firstGood Pd ct.1 with
  | none => fail ct.1
  | some k => ext ct.1 k (pub (ct.1 k) (ct.2 k))

theorem retryOut_bit {C T V O : Type} (N : ℕ) (Pd : C → Prop) (pub : C → T → V)
    (ext : (Fin N → C) → Fin N → V → O) (fail : (Fin N → C) → O) (obs : O → ℚ)
    (ct : (Fin N → C) × (Fin N → T)) :
    obs (retryOut N Pd pub ext fail ct) =
      retryTest N Pd pub (fun c k v => obs (ext c k v)) (fun c => obs (fail c)) ct := by
  unfold retryOut retryTest
  cases firstGood Pd ct.1 <;> rfl

/-! ### The honest retrying prover -/

/-- The commitment phase (REF: prover.rs, host_commitment.rs, state_only_entropy.rs):
from the oracle, one attempt's fresh secrets and the instance, the mask tape
(rejection decode of the expander answers), the three roots, the opening
reads as a function of the challenges, and the exhaustion flag. -/
structure R1Prover (K CommitHandle Aux : Type) [Field K] (F : Subfield K)
    (W : R1Wire K CommitHandle Aux) where
  Secrets : Type
  finSec : Fintype Secrets
  neSec : Nonempty Secrets
  commit : (h : HonestProver K) → (List UInt8 → OracleAnswer) → Secrets → h.Instance →
    Tape K F × (Fin 3 → OracleAnswer) × (Challenges K → List (List UInt8 × OracleAnswer)) × Bool

attribute [instance] R1Prover.finSec R1Prover.neSec

structure AttemptOut (K CommitHandle Aux : Type) [Field K] where
  ch : Challenges K
  view : View K CommitHandle Aux R1Bat
  log : List (List UInt8 × OracleAnswer)
  exh : Bool

section Prover
variable (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)

/-- One honest attempt.  The transcript is run in schedule order; each read's
address uses the answers so far and the messages of the view at the challenges
decoded so far (unanswered blocks read as 0).  The published log is the
verifier's recomputation from the final view. -/
def realAttempt (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (H : List UInt8 → OracleAnswer)
    (sec : Pr.Secrets) : AttemptOut K CommitHandle Aux :=
  let cm := Pr.commit h H sec w
  let step : (TRead → OracleAnswer) → TRead → (TRead → OracleAnswer) := fun tr j =>
    Function.update tr j
      (H (addr j (recP W x (view h B outputs x w (chOf W tr) cm.1) tr cm.2.1)))
  let trF := TranscriptR1.schedule.foldl step (fun _ _ => 0)
  let V := view h B outputs x w (chOf W trF) cm.1
  ⟨chOf W trF, V,
    TranscriptR1.schedule.map (fun j => (addr j (recP W x V trF cm.2.1), H (addr j (recP W x V trF cm.2.1)))) ++
      cm.2.2.1 (chOf W trF),
    cm.2.2.2⟩

/-- The real game: `N` attempts with independent secrets against one oracle;
the first attempt with `P ∧ V ∧ ¬ exhausted` is published with its verifier
log, nothing of the others; the failure exit publishes nothing. -/
def realGame (N : ℕ) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (adv : R1Adv K CommitHandle Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (r : W.Tab × (Fin N → Pr.Secrets)) :
    ROMView K CommitHandle Aux R1Bat :=
  let H := W.look r.1
  let out : Fin N → AttemptOut K CommitHandle Aux := fun k =>
    realAttempt W Pr h B outputs x w H (r.2 k)
  match firstGood (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false) out with
  | none => ⟨W.failView, runLog (adv.prog W.failView []) H W.qmax⟩
  | some k => ⟨(out k).view, (out k).log ++ runLog (adv.prog (out k).view (out k).log) H W.qmax⟩

/-- The R1 Fiat-Shamir experiments. -/
def fsR1 (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    FSExperiments K CommitHandle Aux R1Bat F where
  Adversary := R1Adv K CommitHandle Aux
  RealRand := W.Tab × (Fin N → Pr.Secrets)
  IdealRand := (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)
  real := fun h B outputs adv x w r => realGame W Pr N P Vp h B outputs adv x w r
  ideal := fun sim adv x r =>
    retryOut N (fun c => P (drawW W c)) (fun c t => sim (drawW W c) t)
      (fun c k v => (abR1 W N hN).extend adv x c k v) (fun c => (abR1 W N hN).fail adv x c) r
  observe := fun adv rv => adv.decide rv

instance instRealFin (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Fintype (fsR1 (F := F) W Pr N hN P Vp).RealRand :=
  inferInstanceAs (Fintype (W.Tab × (Fin N → Pr.Secrets)))

instance instRealNe (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Nonempty (fsR1 (F := F) W Pr N hN P Vp).RealRand :=
  inferInstanceAs (Nonempty (W.Tab × (Fin N → Pr.Secrets)))

instance instIdealFin (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Fintype (fsR1 (F := F) W Pr N hN P Vp).IdealRand :=
  inferInstanceAs (Fintype ((Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)))

instance instIdealNe (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) :
    Nonempty (fsR1 (F := F) W Pr N hN P Vp).IdealRand := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  exact inferInstanceAs (Nonempty ((Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)))

end Prover

/-! ### The ideal model: every field proved -/

/-- The identity coupling of a finite uniform type. -/
def idCoupling (R : Type) [Fintype R] [Nonempty R] : Coupling R R where
  S := R
  finS := inferInstance
  nonemptyS := inferInstance
  toR := id
  toM := id
  meanR _ := rfl
  meanM _ := rfl

theorem idealModel_R1 (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (M Umin : ℕ) :
    R1IdealModelV P h V B outputs (fsR1 W Pr N hN P Vp) (abR1 W N hN) x M Umin := by
  intro hx adv
  refine ⟨idCoupling _, fun _ => False, fun _ _ => [], ?_, ?_⟩
  · intro s _
    exact (retryOut_bit N (fun c => P (drawW W c))
      (fun c t => simV h B outputs x hx V (drawW W c) t)
      (fun c k v => (abR1 W N hN).extend adv x c k v) (fun c => (abR1 W N hN).fail adv x c)
      (fun o => bit (adv.decide o)) s).symm
  · intro j j' _ hp
    rcases hp with hp | hp <;> exact False.elim hp

/-- ZF2 form (primary, LOG D44): for ANY simulator, in particular `simE`, the
simulator game of `fsR1` is the abort-middle game, pointwise.  This is the
agreement field of `R1Z.SimulatorR1.R1IdealModelS`. -/
theorem ideal_agree_S (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux) (s : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) :
    middleIdealAbortS P (fsR1 W Pr N hN P Vp) (abR1 W N hN) adv x sim s =
      idealTestS (fsR1 W Pr N hN P Vp) adv x sim s :=
  (retryOut_bit N (fun c => P (drawW W c)) (fun c t => sim (drawW W c) t)
    (fun c k v => (abR1 W N hN).extend adv x c k v) (fun c => (abR1 W N hN).fail adv x c)
    (fun o => bit (adv.decide o)) s).symm

/-- The body of `R1IdealModelS` for `fsR1` / `abR1` and any simulator: the
identity coupling, agreement everywhere, no private position. -/
theorem idealModelS_body (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) (x : Statement K CommitHandle)
    (M Umin : ℕ) (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux) :
    ∃ (cp : Coupling (fsR1 W Pr N hN P Vp).IdealRand
        ((Fin (abR1 W N hN).N → (abR1 W N hN).Coins) × (Fin (abR1 W N hN).N → Tape K F)))
      (priv : Fin M → Prop) (addr : Fin M → cp.S → List UInt8),
      (∀ s, ¬ CollEv M priv addr s →
        middleIdealAbortS P (fsR1 W Pr N hN P Vp) (abR1 W N hN) adv x sim (cp.toM s) =
          idealTestS (fsR1 W Pr N hN P Vp) adv x sim (cp.toR s)) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        PairFresh (addr j) (addr j') Umin ∨ PairFresh (addr j') (addr j) Umin) := by
  refine ⟨idCoupling _, fun _ => False, fun _ _ => [], ?_, ?_⟩
  · intro s _
    exact ideal_agree_S W Pr N hN P Vp x sim adv s
  · intro j j' _ hp
    rcases hp with hp | hp <;> exact False.elim hp

/-! ### Coordinate lenses on the attempt coins -/

section Lenses
variable (W : R1Wire K CommitHandle Aux)

def ksC (c : R1Coins W.Cm W.Tab) : Fin 8 := W.kstarOf (fun k => c.1 (.qb k))

theorem ksC_congr (c c' : R1Coins W.Cm W.Tab) (h : ∀ k, c.1 (.qb k) = c'.1 (.qb k)) :
    ksC W c = ksC W c' := by
  unfold ksC
  rw [show (fun k => c.1 (.qb k)) = (fun k => c'.1 (.qb k)) from funext h]

theorem chOf_congr (tr tr' : TRead → OracleAnswer) (h : ∀ j, IsSq j → tr j = tr' j) :
    chOf (K := K) W tr = chOf W tr' := by
  unfold chOf
  rw [show (fun i => tr (.sqS i)) = (fun i => tr' (.sqS i)) from funext fun i => h _ trivial,
    show (fun i => tr (.sqO i)) = (fun i => tr' (.sqO i)) from funext fun i => h _ trivial,
    show (fun k => tr (.qb k)) = (fun k => tr' (.qb k)) from funext fun k => h _ trivial,
    h .sqR trivial]

theorem ksC_update_qa (c : R1Coins W.Cm W.Tab) (m : Fin 8) (u : OracleAnswer) :
    ksC W (Function.update c.1 (.qa m) u, c.2) = ksC W c :=
  ksC_congr W _ _ (fun k => Function.update_of_ne (show TRead.qb k ≠ TRead.qa m by simp) u c.1)

def coinLens : Coord → Lens (R1Coins W.Cm W.Tab) OracleAnswer
  | .root =>
    { get := fun c => c.2.1 0
      set := fun c u => (c.1, Function.update c.2.1 0 u, c.2.2)
      get_set := fun c u => by simp
      set_get := fun c => by simp
      set_set := fun c u u' => by simp }
  | .ans j =>
    { get := fun c => c.1 j
      set := fun c u => (Function.update c.1 j u, c.2)
      get_set := fun c u => by simp
      set_get := fun c => by simp
      set_set := fun c u u' => by simp }
  | .sel =>
    { get := fun c => c.1 (.qa (ksC W c))
      set := fun c u => (Function.update c.1 (.qa (ksC W c)) u, c.2)
      get_set := fun c u => by
        show Function.update c.1 (.qa (ksC W c)) u
          (.qa (ksC W (Function.update c.1 (.qa (ksC W c)) u, c.2))) = u
        rw [ksC_update_qa]
        simp
      set_get := fun c => by simp
      set_set := fun c u u' => by
        show (Function.update (Function.update c.1 (.qa (ksC W c)) u)
            (.qa (ksC W (Function.update c.1 (.qa (ksC W c)) u, c.2))) u', c.2) =
          (Function.update c.1 (.qa (ksC W c)) u', c.2)
        rw [ksC_update_qa]
        simp }

/-- A chain lens leaves every squeeze answer, the commitment answers and the
table unchanged. -/
theorem coinLens_sq (c : Coord) (hc : ChainC c) (cc : R1Coins W.Cm W.Tab) (u : OracleAnswer)
    (j : TRead) (hj : IsSq j) : ((coinLens W c).set cc u).1 j = cc.1 j := by
  cases c with
  | root => rfl
  | sel =>
      show Function.update cc.1 (.qa (ksC W cc)) u j = cc.1 j
      refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact hj
  | ans j0 =>
      show Function.update cc.1 j0 u j = cc.1 j
      refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact hc _ rfl hj

theorem coinLens_tail (c : Coord) (cc : R1Coins W.Cm W.Tab) (u : OracleAnswer) :
    ((coinLens W c).set cc u).2.2 = cc.2.2 := by
  cases c <;> rfl

theorem drawW_coinLens (c : Coord) (hc : ChainC c) (cc : R1Coins W.Cm W.Tab) (u : OracleAnswer) :
    drawW (K := K) W ((coinLens W c).set cc u) = drawW W cc :=
  chOf_congr W _ _ (fun j hj => coinLens_sq W c hc cc u j hj)

/-- The lens of coordinate `c` of attempt `k` on the abort-middle coins. -/
abbrev midLens (N : ℕ) (k : Fin N) (c : Coord) :
    Lens ((Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) OracleAnswer :=
  Lens.pi k (coinLens W c)

/-- The record of attempt `k` in the middle game. -/
def attR (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (w : h.Instance) {N : ℕ} (ct : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F))
    (k : Fin N) : Rec :=
  recP W x (view h B outputs x w (drawW W (ct.1 k)) (ct.2 k)) (ct.1 k).1 (ct.1 k).2.1

theorem attR_same (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (w : h.Instance) {N : ℕ} (k : Fin N) (c : Coord) (hc : ChainC c)
    (ct : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) (u : OracleAnswer) :
    attR W h B outputs x w ((midLens W N k c).set ct u) k = setC c (attR W h B outputs x w ct k) u := by
  unfold attR
  rw [Lens.pi_set_fst_eq, Lens.pi_set_snd, drawW_coinLens W c hc]
  cases c with
  | root =>
      show recP W x _ (ct.1 k).1 (Function.update (ct.1 k).2.1 0 u) = _
      simp only [recP, setC]
      rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      all_goals rfl
  | sel =>
      show recP W x _ (Function.update (ct.1 k).1 (.qa (ksC W (ct.1 k))) u) (ct.1 k).2.1 = _
      simp only [recP, setC]
      have hk : W.kstarOf (fun m => Function.update (ct.1 k).1 (.qa (ksC W (ct.1 k))) u (.qb m)) =
          W.kstarOf (fun m => (ct.1 k).1 (.qb m)) :=
        ksC_update_qa W (ct.1 k) (ksC W (ct.1 k)) u
      rw [hk]
      all_goals rfl
  | ans j =>
      show recP W x _ (Function.update (ct.1 k).1 j u) (ct.1 k).2.1 = _
      simp only [recP, setC]
      have hk : W.kstarOf (fun m => Function.update (ct.1 k).1 j u (.qb m)) =
          W.kstarOf (fun m => (ct.1 k).1 (.qb m)) :=
        ksC_congr W (Function.update (ct.1 k).1 j u, (ct.1 k).2) (ct.1 k)
          (fun m => coinLens_sq W (.ans j) hc (ct.1 k) u (.qb m) trivial)
      rw [hk]
      all_goals rfl

theorem attR_other (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (w : h.Instance) {N : ℕ} (k k' : Fin N) (c : Coord)
    (ct : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) (u : OracleAnswer) (hk : k' ≠ k) :
    attR W h B outputs x w ((midLens W N k c).set ct u) k' = attR W h B outputs x w ct k' := by
  unfold attR
  rw [Lens.pi_set_fst_ne _ _ _ _ _ hk, Lens.pi_set_snd]

end Lenses

/-! ### The real model -/

section Real
variable (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
  (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)

abbrev Mid := (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)

/-- The accepted attempt of the middle game (`P ∧ V` on the drawn challenges). -/
def accR (w : h.Instance) (ct : Mid (F := F) W N) : Option (Fin N) :=
  firstGood (fun c => P (drawW W c) ∧ V (drawW W c) w) ct.1

/-- Attempt `k` was run and discarded. -/
def discR (w : h.Instance) (k : Fin N) (ct : Mid (F := F) W N) : Prop :=
  match accR W N P h V w ct with
  | none => True
  | some k₀ => k < k₀

/-- The adversary's own log in the middle game (as in `extend` / `fail`). -/
def advLogR (w : h.Instance) (adv : R1Adv K CommitHandle Aux) (ct : Mid (F := F) W N) :
    List (List UInt8 × OracleAnswer) :=
  match accR W N P h V w ct with
  | none => runLog (adv.prog W.failView []) (W.look (ct.1 ⟨0, hN⟩).2.2.2) W.qmax
  | some k₀ =>
      runLog (adv.prog (view h B outputs x w (drawW W (ct.1 k₀)) (ct.2 k₀))
          (verLog W x (view h B outputs x w (drawW W (ct.1 k₀)) (ct.2 k₀)) (ct.1 k₀)))
        (progOracle W x (view h B outputs x w (drawW W (ct.1 k₀)) (ct.2 k₀)) (ct.1 k₀)
          (ct.1 ⟨0, hN⟩).2.2.2) W.qmax

def qryR (w : h.Instance) (adv : R1Adv K CommitHandle Aux) (i : Fin W.qmax)
    (ct : Mid (F := F) W N) : List UInt8 :=
  ((advLogR W N hN P h V B outputs x w adv ct).getD i.val ([], fun _ => 0)).1

theorem accR_midLens (w : h.Instance) (k : Fin N) (c : Coord) (hc : ChainC c)
    (ct : Mid (F := F) W N) (u : OracleAnswer) :
    accR W N P h V w ((midLens W N k c).set ct u) = accR W N P h V w ct := by
  unfold accR
  have e1 : firstGood (fun c => P (drawW W c) ∧ V (drawW W c) w) ((midLens W N k c).set ct u).1 =
      firstGood (fun j => P (drawW W (((midLens W N k c).set ct u).1 j)) ∧
        V (drawW W (((midLens W N k c).set ct u).1 j)) w) id := rfl
  have e2 : firstGood (fun c => P (drawW W c) ∧ V (drawW W c) w) ct.1 =
      firstGood (fun j => P (drawW W (ct.1 j)) ∧ V (drawW W (ct.1 j)) w) id := rfl
  rw [e1, e2]
  apply firstGood_congr
  intro j
  dsimp only [id]
  by_cases hj : j = k
  · rw [hj, show ((midLens W N k c).set ct u).1 k = (coinLens W c).set (ct.1 k) u from
      Lens.pi_set_fst_eq _ _ _ _, drawW_coinLens W c hc]
  · rw [show ((midLens W N k c).set ct u).1 j = ct.1 j from Lens.pi_set_fst_ne _ _ _ _ _ hj]

theorem tab0_midLens (k : Fin N) (c : Coord) (ct : Mid (F := F) W N) (u : OracleAnswer)
    (j : Fin N) : (((midLens W N k c).set ct u).1 j).2.2.2 = (ct.1 j).2.2.2 := by
  by_cases hj : j = k
  · rw [hj, show ((midLens W N k c).set ct u).1 k = (coinLens W c).set (ct.1 k) u from
      Lens.pi_set_fst_eq _ _ _ _, coinLens_tail]
  · rw [show ((midLens W N k c).set ct u).1 j = ct.1 j from Lens.pi_set_fst_ne _ _ _ _ _ hj]

/-- On a discarded attempt, the adversary's reads do not see its coordinates. -/
theorem advLogR_midLens (w : h.Instance) (adv : R1Adv K CommitHandle Aux) (k : Fin N) (c : Coord)
    (hc : ChainC c) (ct : Mid (F := F) W N) (u : OracleAnswer) (hd : discR W N P h V w k ct) :
    advLogR W N hN P h V B outputs x w adv ((midLens W N k c).set ct u) =
      advLogR W N hN P h V B outputs x w adv ct := by
  unfold advLogR
  rw [accR_midLens W N P h V w k c hc ct u]
  rcases ha : accR W N P h V w ct with _ | k₀
  · simp only [tab0_midLens]
  · have hd' : k < k₀ := by
      unfold discR at hd
      rw [ha] at hd
      exact hd
    have hne : k₀ ≠ k := fun e => by subst e; exact lt_irrefl _ hd'
    simp only [tab0_midLens,
      show ((midLens W N k c).set ct u).1 k₀ = ct.1 k₀ from Lens.pi_set_fst_ne _ _ _ _ _ hne,
      show ((midLens W N k c).set ct u).2 = ct.2 from rfl]

theorem discR_midLens (w : h.Instance) (k k' : Fin N) (c : Coord) (hc : ChainC c)
    (ct : Mid (F := F) W N) (u : OracleAnswer) :
    discR W N P h V w k' ((midLens W N k c).set ct u) = discR W N P h V w k' ct := by
  unfold discR
  rw [accR_midLens W N P h V w k c hc ct u]

/-- The commitment-read layout (H-layout for salts, leaves, nodes, expander
and seed reads; design §6.3), on the real coupling space. -/
structure CmLayout (S : Type) [Fintype S] (q Mc : ℕ) (qry : Fin q → S → List UInt8)
    (Lc : Fin N → Coord → Lens S OracleAnswer) where
  charged : Fin N → Fin Mc → S → Prop
  priv : Fin N → Fin Mc → Prop
  caddr : Fin N → Fin Mc → S → List UInt8
  hit : ∀ k c i, HitFresh (charged k c) (qry i) (caddr k c) (2 ^ 255)
  pair : ∀ p p' : Fin N × Fin Mc, p ≠ p' → (priv p.1 p.2 ∨ priv p'.1 p'.2) →
    PairFresh (caddr p.1 p.2) (caddr p'.1 p'.2) (2 ^ 255) ∨
      PairFresh (caddr p'.1 p'.2) (caddr p.1 p.2) (2 ^ 255)
  cross : ∀ k c k' coord s u, ChainC coord → caddr k c ((Lc k' coord).set s u) = caddr k c s

/-- The data of the real coupling for one adversary and witness: the coupling
(G-prog: lazy programming, with `toM` a coordinate projection — `hLc`), the
commitment layout, and the exhaustion event. -/
structure R1RealData (adv : R1Adv K CommitHandle Aux) (w : h.Instance) (Mc : ℕ) where
  cp : Coupling (fsR1 (F := F) W Pr N hN P Vp).RealRand (Mid (F := F) W N)
  Lc : Fin N → Coord → Lens cp.S OracleAnswer
  hLc : ∀ k c s u, cp.toM ((Lc k c).set s u) = (midLens W N k c).set (cp.toM s) u
  cm : CmLayout N cp.S W.qmax Mc
    (fun i s => qryR W N hN P h V B outputs x w adv i (cp.toM s)) Lc
  exh : cp.S → Prop

variable {W Pr N hN P Vp h V B outputs x}

def R1RealData.frame {adv : R1Adv K CommitHandle Aux} {w : h.Instance} {Mc : ℕ}
    (d : R1RealData W Pr N hN P Vp h V B outputs x adv w Mc) : TranscriptFrame d.cp.S N where
  att k s := attR W h B outputs x w (d.cp.toM s) k
  lens := d.Lc
  rec_same k c s u hc := by
    show attR W h B outputs x w (d.cp.toM ((d.Lc k c).set s u)) k = _
    rw [d.hLc]
    exact attR_same W h B outputs x w k c hc _ u
  rec_other k k' c s u hk := by
    show attR W h B outputs x w (d.cp.toM ((d.Lc k c).set s u)) k' = _
    rw [d.hLc]
    exact attR_other W h B outputs x w k k' c _ u hk

abbrev Pos (N Mc : ℕ) := Fin N × (TRead ⊕ Fin Mc)

theorem card_pos (Mc : ℕ) : Fintype.card (Pos N Mc) = N * (115 + Mc) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, card_TRead, Fintype.card_fin]

def posEquiv (Mc : ℕ) : Fin (N * (115 + Mc)) ≃ Pos N Mc :=
  (Fintype.equivFinOfCardEq (card_pos (N := N) Mc)).symm

section Events
variable {adv : R1Adv K CommitHandle Aux} {w : h.Instance} {Mc : ℕ}
  (d : R1RealData W Pr N hN P Vp h V B outputs x adv w Mc)

def R1RealData.chargedP (p : Pos N Mc) : d.cp.S → Prop :=
  Sum.elim (fun _ s => discR W N P h V w p.1 (d.cp.toM s)) (fun c => d.cm.charged p.1 c) p.2

def R1RealData.privP (p : Pos N Mc) : Prop :=
  Sum.elim (fun _ => True) (fun c => d.cm.priv p.1 c) p.2

def R1RealData.addrP (p : Pos N Mc) : d.cp.S → List UInt8 :=
  Sum.elim (fun j => taddr d.frame p.1 j) (fun c => d.cm.caddr p.1 c) p.2

def R1RealData.qryS (i : Fin W.qmax) (s : d.cp.S) : List UInt8 :=
  qryR W N hN P h V B outputs x w adv i (d.cp.toM s)

/-- Agreement of the real game with the middle game outside the events
(G-ref: the Rust prover refines `realAttempt`, and the real oracle equals the
programmed table off the charged reads). -/
def R1RealData.Agree : Prop :=
  ∀ s, ¬ HitEv (N * (115 + Mc)) W.qmax (fun i => d.chargedP (posEquiv Mc i)) d.qryS
      (fun i => d.addrP (posEquiv Mc i)) s →
    ¬ (CollEv (N * (115 + Mc)) (fun i => d.privP (posEquiv Mc i))
        (fun i => d.addrP (posEquiv Mc i)) s ∨ d.exh s) →
    realTest h B outputs (fsR1 W Pr N hN P Vp) adv x w (d.cp.toR s) =
      middleRealAbortV P h V B outputs (fsR1 W Pr N hN P Vp) (abR1 W N hN) adv x w (d.cp.toM s)

theorem R1RealData.hit (p : Pos N Mc) (i : Fin W.qmax) :
    HitFresh (d.chargedP p) (d.qryS i) (d.addrP p) (2 ^ 255) := by
  obtain ⟨k, j | c⟩ := p
  · refine hitFresh_transcript d.frame k j _ _ ?_ ?_
    · intro s u hs
      show discR W N P h V w k (d.cp.toM ((d.Lc k (fc j)).set s u))
      rw [d.hLc, discR_midLens W N P h V w k k (fc j) (chain_fc j)]
      exact hs
    · intro s u hs
      show ((advLogR W N hN P h V B outputs x w adv (d.cp.toM ((d.Lc k (fc j)).set s u))).getD
          i.val ([], fun _ => 0)).1 =
        ((advLogR W N hN P h V B outputs x w adv (d.cp.toM s)).getD i.val ([], fun _ => 0)).1
      rw [d.hLc, advLogR_midLens W N hN P h V B outputs x w adv k (fc j) (chain_fc j) _ u hs]
  · exact d.cm.hit k c i

theorem R1RealData.pair (p p' : Pos N Mc) (hne : p ≠ p') (hpr : d.privP p ∨ d.privP p') :
    PairFresh (d.addrP p) (d.addrP p') (2 ^ 255) ∨ PairFresh (d.addrP p') (d.addrP p) (2 ^ 255) := by
  obtain ⟨k, j | c⟩ := p <;> obtain ⟨k', j' | c'⟩ := p'
  · have hne' : (k, j) ≠ (k', j') := fun e => hne (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rfl)
    exact pairFresh_transcript d.frame (k, j) (k', j') hne'
  · refine Or.inr (pairFresh_of_lens (d.Lc k (fc j)) _ _ (extract j) _ umin_le_card_ans ?_
      (taddr_extract d.frame k j))
    intro s u
    exact d.cm.cross k' c' k (fc j) s u (chain_fc j)
  · refine Or.inl (pairFresh_of_lens (d.Lc k' (fc j')) _ _ (extract j') _ umin_le_card_ans ?_
      (taddr_extract d.frame k' j'))
    intro s u
    exact d.cm.cross k c k' (fc j') s u (chain_fc j')
  · have hne' : (k, c) ≠ (k', c') := fun e => hne (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rfl)
    exact d.cm.pair (k, c) (k', c') hne' hpr

end Events

/-- The real model from the R1 games: the transcript freshness tables, the
cross pairs and the position count are proved; the coupling, agreement,
commitment layout and exhaustion mass are the `R1RealData` hypotheses. -/
theorem realModel_R1 (Mc : ℕ) (εexh : ℚ)
    (hd : ∀ (adv : R1Adv K CommitHandle Aux) (w : h.Instance), h.public w = x.1 →
      ∃ d : R1RealData W Pr N hN P Vp h V B outputs x adv w Mc,
        d.Agree ∧ mass d.exh ≤ εexh) :
    R1RealModelV P h V B outputs (fsR1 W Pr N hN P Vp) (abR1 W N hN) x
      (N * (115 + Mc)) W.qmax (2 ^ 255) εexh := by
  intro adv w hw
  obtain ⟨d, hag, hex⟩ := hd adv w hw
  refine ⟨d.cp, fun i => d.chargedP (posEquiv Mc i), fun i => d.privP (posEquiv Mc i),
    fun i => d.addrP (posEquiv Mc i), d.qryS, d.exh, hag, ?_, ?_, hex⟩
  · intro j i
    exact d.hit (posEquiv Mc j) i
  · intro j j' hj hp
    exact d.pair (posEquiv Mc j) (posEquiv Mc j')
      (fun e => (ne_of_lt hj) ((posEquiv Mc).injective e)) hp

end Real

#print axioms runLog
#print axioms abR1
#print axioms retryOut_bit
#print axioms realAttempt
#print axioms fsR1
#print axioms idCoupling
#print axioms idealModel_R1
#print axioms ideal_agree_S
#print axioms idealModelS_body
#print axioms coinLens
#print axioms coinLens_sq
#print axioms drawW_coinLens
#print axioms attR_same
#print axioms attR_other
#print axioms accR_midLens
#print axioms advLogR_midLens
#print axioms discR_midLens
#print axioms R1RealData.frame
#print axioms card_pos
#print axioms R1RealData.hit
#print axioms R1RealData.pair
#print axioms realModel_R1
end R1Z.GamesR1
