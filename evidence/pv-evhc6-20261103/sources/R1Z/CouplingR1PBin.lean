import R1Z.GamesR1PBin
import R0Z.FsAbortTape

-- Binary-format copy of `R1Z.CouplingR1P` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! The real coupling of the phase-indexed games (DESIGN-R1-REAL §4).

Coupling space `SP = Fin N → AttS`, one block per attempt:
`AttS = SecP × (Pos1 → Ans) × Tape × Tab` — the attempt secrets, an
independent uniform answer for every read of the attempt (transcript and
commitment), a spare tape and a spare table (attempt 0's table is the base
table of the oracle).

* `toMP` (to the middle game of `abR1`): attempt `k`'s coins are its
  transcript answers, its three root answers, its `RIdx` answers (as the
  `Cm` coin through `eCm`) and its table; its tape is the mask decode of its
  expander answers, or the spare tape on exhaustion.  `meanM_P`: uniform,
  from the decoder's equal fibres (`mean_decodeOrSpare`).
* `toRP` (to the real game): the base table reprogrammed at every read
  address of every attempt with the lazy answers (frozen digest address,
  `LazyFrozen.progF`), and the secrets.  `meanR_P`: uniform, from the frozen
  lazy-programming law and the causality premise `RCausal`.

Premises named here: `RomModel` (R-rom: the random oracle is a uniform table
on a finite domain of byte strings; `look` is evaluation, 0 off the domain),
`RAddrIn` (every prover address is in that domain), `RCausal` (R-causal: an
address depends only on the answers of earlier reads in `ord`). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.CouplingR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
attribute [local instance] Classical.propDecidable

/-! ### Measure-preserving maps -/

def MP {X Y : Type} [Fintype X] [Fintype Y] (g : X → Y) : Prop :=
  ∀ f : Y → ℚ, mean (fun x => f (g x)) = mean f

theorem mp_comp {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {g : X → Y} {g' : Y → Z}
    (h : MP g) (h' : MP g') : MP (fun x => g' (g x)) :=
  fun f => (h (fun y => f (g' y))).trans (h' f)

theorem mp_equiv {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y) : MP e := by
  intro f
  rw [mean_equiv' e (fun x => f (e x))]
  simp

theorem mean_comm {X Y : Type} [Fintype X] [Fintype Y] (F : X → Y → ℚ) :
    mean (fun x => mean (fun y => F x y)) = mean (fun y => mean (fun x => F x y)) := by
  unfold mean
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.sum_div, div_div, mul_comm]

theorem mp_fst {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] : MP (Prod.fst : X × Y → X) := by
  intro f
  rw [LawTransport.mean_product]
  simp only [mean_const']

theorem mp_snd {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] : MP (Prod.snd : X × Y → Y) := by
  intro f
  rw [LawTransport.mean_product, mean_comm]
  simp only [mean_const']

theorem mp_prodMap {X₁ X₂ Y₁ Y₂ : Type} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    {g₁ : X₁ → Y₁} {g₂ : X₂ → Y₂} (h₁ : MP g₁) (h₂ : MP g₂) :
    MP (fun p : X₁ × X₂ => (g₁ p.1, g₂ p.2)) := by
  intro f
  rw [LawTransport.mean_product, LawTransport.mean_product (f := f)]
  simp only []
  have e1 : ∀ x₁, mean (fun x₂ => f (g₁ x₁, g₂ x₂)) = mean (fun y₂ => f (g₁ x₁, y₂)) :=
    fun x₁ => h₂ (fun y₂ => f (g₁ x₁, y₂))
  simp only [e1]
  rw [mean_comm, mean_comm (fun y₁ y₂ => f (y₁, y₂))]
  congr 1
  funext y₂
  exact h₁ (fun y₁ => f (y₁, y₂))

theorem mp_pi {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] {g : X → Y} (h : MP g) :
    ∀ N : ℕ, MP (fun (x : Fin N → X) (k : Fin N) => g (x k))
  | 0 => by
      intro f
      have hu : ∀ x : Fin 0 → X, (fun k => g (x k)) = (default : Fin 0 → Y) :=
        fun x => Subsingleton.elim _ _
      simp only [hu, mean_const']
      unfold mean
      rw [Fintype.sum_unique, Fintype.card_unique]
      simp
  | N + 1 => by
      have hc := mp_comp (mp_comp (mp_equiv (Fin.consEquiv (fun _ => X)).symm)
        (mp_prodMap h (mp_pi h N))) (mp_equiv (Fin.consEquiv (fun _ => Y)))
      intro f
      have e : (fun x : Fin (N + 1) → X => f (fun k => g (x k))) =
          (fun x => f ((Fin.consEquiv (fun _ => Y))
            (g ((Fin.consEquiv (fun _ => X)).symm x).1,
              fun k => g (((Fin.consEquiv (fun _ => X)).symm x).2 k)))) := by
        funext x
        congr 1
        funext k
        refine Fin.cases ?_ (fun i => ?_) k
        · rfl
        · rfl
      rw [e]
      exact hc f

/-! ### The random-oracle model and the premises -/

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- R-rom: the oracle is a uniform table on a finite domain `A` of byte
strings (every hash input of the protocol has bounded length); `look` is
evaluation, and 0 off the domain. -/
structure RomModel (W : R1Wire K CommitHandle Aux) where
  A : Type
  finA : Fintype A
  deqA : DecidableEq A
  neA : Nonempty A
  dec : List UInt8 → Option A
  enc : A → List UInt8
  dec_enc : ∀ a, dec (enc a) = some a
  enc_of_dec : ∀ b a, dec b = some a → enc a = b
  eTab : W.Tab ≃ (A → OracleAnswer)
  look_eq : ∀ tab b, W.look tab b = match dec b with
    | some a => eTab tab a
    | none => 0

attribute [instance] RomModel.finA RomModel.deqA RomModel.neA

section Model
variable {W : R1Wire K CommitHandle Aux} (R : RomModel W)

def lookA (T : R.A → OracleAnswer) (b : List UInt8) : OracleAnswer :=
  match R.dec b with
  | some a => T a
  | none => 0

theorem look_eqA (tab : W.Tab) (b : List UInt8) : W.look tab b = lookA R (R.eTab tab) b := by
  rw [R.look_eq]
  unfold lookA
  cases R.dec b <;> rfl

/-- The frozen addresses: the statement digest's input `public_bytes`. -/
def Frz (x : Statement K CommitHandle) : Finset R.A :=
  match R.dec (W.pubBytes x) with
  | some a => {a}
  | none => ∅

theorem lookA_frozen (x : Statement K CommitHandle) (T T' : R.A → OracleAnswer)
    (h : ∀ y ∈ Frz R x, T y = T' y) : lookA R T (W.pubBytes x) = lookA R T' (W.pubBytes x) := by
  unfold lookA
  unfold Frz at h
  split
  · next a ha =>
      rw [ha] at h
      exact h a (Finset.mem_singleton_self a)
  · rfl

end Model

section Coupling
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer))
  (h : HonestProver K) (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

/-- Every prover read address lies in the oracle's domain. -/
def RAddrIn : Prop :=
  ∀ (sec : SecP) (d : OracleAnswer) (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (p : Pos1 Pr.E₁ Pr.E₂),
    (R.dec (attAddr W Pr h B outputs x w sec d v p)).isSome

/-- R-causal: in the prover's order `ord`, every read's address (transcript
or commitment; roots, challenges and tape evaluated on the answers so far)
depends only on the answers of the earlier reads. -/
def RCausal : Prop :=
  ∀ (sec : SecP) (d : OracleAnswer) (i : Fin (n1 W Pr)) (v v' : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer),
    (∀ j, j < i → v (Pr.ord j) = v' (Pr.ord j)) →
      attAddr W Pr h B outputs x w sec d v (Pr.ord i) = attAddr W Pr h B outputs x w sec d v' (Pr.ord i)

abbrev AttS := SecP × (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × Tape K F × W.Tab

/-- The lazy answers of all attempts as one vector (attempt-major, `ord`). -/
def uVec {N : ℕ} (s : Fin N → AttS (F := F) W Pr) : Fin (N * n1 W Pr) → OracleAnswer :=
  fun g => (s (finProdFinEquiv.symm g).1).2.1 (Pr.ord (finProdFinEquiv.symm g).2)

theorem attVec_uVec {N : ℕ} (s : Fin N → AttS (F := F) W Pr) (k : Fin N) :
    attVec W Pr (uVec W Pr s) k = (s k).2.1 := by
  funext p
  simp [attVec, uVec]

/-- The global read program with addresses in the oracle domain. -/
def aA {N : ℕ} (sec : Fin N → SecP) (g : Fin (N * n1 W Pr)) (V : Fin (N * n1 W Pr) → OracleAnswer)
    (T : R.A → OracleAnswer) : R.A :=
  (R.dec (gAddr W Pr h B outputs x w sec (lookA R T (W.pubBytes x)) g V)).getD
    (Classical.arbitrary R.A)

theorem enc_aA (hin : RAddrIn W Pr R h B outputs x w) {N : ℕ} (sec : Fin N → SecP)
    (g : Fin (N * n1 W Pr)) (V : Fin (N * n1 W Pr) → OracleAnswer) (T : R.A → OracleAnswer) :
    R.enc (aA W Pr R h B outputs x w sec g V T) =
      gAddr W Pr h B outputs x w sec (lookA R T (W.pubBytes x)) g V := by
  unfold aA
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hin _ _ _ _)
  unfold gAddr
  rw [ha]
  exact R.enc_of_dec _ _ ha

theorem fPF_lt {N n : ℕ} (k : Fin N) (j i : Fin n) (h : j < i) :
    finProdFinEquiv (k, j) < finProdFinEquiv (k, i) := by
  show j.val + n * k.val < i.val + n * k.val
  have := Fin.lt_def.mp h
  omega

theorem causalF_aA (hc : RCausal W Pr h B outputs x w) {N : ℕ} (sec : Fin N → SecP) :
    CausalF (Frz R x) (aA W Pr R h B outputs x w sec) := by
  intro g V V' T T' hV hT
  unfold aA gAddr
  rw [lookA_frozen R x T T' hT]
  congr 2
  refine hc _ _ _ _ _ (fun j hj => ?_)
  unfold attVec
  rw [Equiv.symm_apply_apply]
  refine hV _ ?_
  have hg : finProdFinEquiv ((finProdFinEquiv.symm g).1, (finProdFinEquiv.symm g).2) = g :=
    Equiv.apply_symm_apply _ _
  conv_rhs => rw [← hg]
  exact fPF_lt _ _ _ hj

/-! ### The two maps -/

def toRP {N : ℕ} (hN : 0 < N) (s : Fin N → AttS (F := F) W Pr) : W.Tab × (Fin N → SecP) :=
  (R.eTab.symm (progF (Frz R x) (aA W Pr R h B outputs x w (fun k => (s k).1))
    (R.eTab (s ⟨0, hN⟩).2.2.2) (uVec W Pr s)), fun k => (s k).1)

/-- One attempt's middle coins and tape. -/
def gM (a : AttS (F := F) W Pr) : R1Coins W.Cm W.Tab × Tape K F :=
  ((trOf a.2.1, rootsOf a.2.1, eCm.symm (restOf a.2.1), a.2.2.2),
    (Pr.tapeOf (e₁Of a.2.1) (e₂Of a.2.1)).getD a.2.2.1)

def toMP {N : ℕ} (s : Fin N → AttS (F := F) W Pr) :
    (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F) :=
  (fun k => (gM W Pr eCm (s k)).1, fun k => (gM W Pr eCm (s k)).2)

end Coupling

#print axioms mp_pi
#print axioms mp_prodMap
#print axioms enc_aA
#print axioms causalF_aA
#print axioms mp_comp
#print axioms mp_equiv
#print axioms mean_comm
#print axioms mp_fst
#print axioms mp_snd
#print axioms look_eqA
#print axioms lookA_frozen
#print axioms attVec_uVec
#print axioms fPF_lt
end R1Z.CouplingR1PBin
