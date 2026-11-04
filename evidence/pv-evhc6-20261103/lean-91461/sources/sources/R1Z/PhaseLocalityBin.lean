import R1Z.PhaseScheduleBin
import R1Z.CausalPremisesR1PBin

/-! Dependency contracts on the *evaluated* protocol messages. These quantify
over all answer vectors, including unsuccessful/exhausted attempts. They are
not certificates that the shipped encoding satisfies the contracts. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseLocalityBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.LayoutR1PBin R1Z.TranscriptR1 R1Z.PhaseScheduleBin

def SqAgree (cut : ℕ) (tr tr' : TRead → OracleAnswer) : Prop :=
  ∀ j, IsSq j → transcriptStage j < cut → tr j = tr' j

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Componentwise squeeze-row dependencies, without a sampling-law assumption. -/
structure DecodeLocal (dec : (Fin 27 → OracleAnswer) → (Fin 4 → OracleAnswer) →
    (Fin 8 → OracleAnswer) → OracleAnswer → Challenges K) : Prop where
  sem : ∀ s s' o o' q q' r r' (i : Fin 25),
    s ⟨i.val, by omega⟩ = s' ⟨i.val, by omega⟩ →
    (dec s o q r).sem i = (dec s' o' q' r').sem i
  circle : ∀ s s' o o' q q' r r' (i : Fin 2),
    s ⟨25 + i.val, by omega⟩ = s' ⟨25 + i.val, by omega⟩ →
    (dec s o q r).circle i = (dec s' o' q' r').circle i
  opening : ∀ s s' o o' q q' r r' i, o i = o' i →
    (dec s o q r).opening i = (dec s' o' q' r').opening i
  queries : ∀ s s' o o' q r r', (dec s o q r).queries = (dec s' o' q r').queries

/-- The original wire together with phase-local message contracts at the
specified experiment. In particular arbitrary auxiliary outputs cannot leak
future challenges through the encoding. -/
structure R1PhaseWire (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) where
  toWire : R1Wire K CommitHandle Aux
  decode_local : DecodeLocal toWire.dec
  frame_local : ∀ (w : h.Instance) τ tr tr' r r' i,
    SqAgree (transcriptStage (.absS i)) tr tr' → (i.val = 2 → r = r') →
    toWire.frame (view h B outputs x w (chOf toWire tr) τ) r i =
      toWire.frame (view h B outputs x w (chOf toWire tr') τ) r' i
  payload_local : ∀ (w : h.Instance) τ tr tr' r r' i,
    SqAgree (transcriptStage (.absO i)) tr tr' → (i.val = 3 → r = r') →
    toWire.payload (view h B outputs x w (chOf toWire tr) τ) r i =
      toWire.payload (view h B outputs x w (chOf toWire tr') τ) r' i
  final_local : ∀ (w : h.Instance) τ tr tr', SqAgree (transcriptStage .absQ) tr tr' →
    toWire.final (view h B outputs x w (chOf toWire tr) τ) =
      toWire.final (view h B outputs x w (chOf toWire tr') τ)

/-- A refinement of a prover's data: caddr and ord are constructed, rather
than accepted as arbitrary functions. The C1 cutoff admits no squeeze, C2
admits only semantic rows 0 and 1, folded admits rows through 29. -/
structure R1PhaseProver (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (W : R1PhaseWire h B outputs x) where
  data : R1ProverP K CommitHandle Aux F W.toWire
  leaf_local : ∀ (w : h.Instance) τ tr tr' T u,
    SqAgree (treeBase T + 6) tr tr' →
    data.leafVal h w x τ (chOf W.toWire tr) T u =
      data.leafVal h w x τ (chOf W.toWire tr') T u

abbrev R1PhaseProver.toProver {h : HonestProver K} {B : PackBasis F}
    {outputs : Statement K CommitHandle → Challenges K → Aux}
    {x : Statement K CommitHandle} {W : R1PhaseWire h B outputs x}
    (P : R1PhaseProver h B outputs x W) : R1ProverP K CommitHandle Aux F W.toWire :=
  { P.data with
    caddr := fun h w x sec d τ rest ch =>
      gram (W.toWire.pubBytes x) W.toWire.vtag (P.data.leafVal h w x τ ch) sec d rest
    ord := PhaseScheduleBin.ord P.data.E₁ P.data.E₂ }

/-- Pointwise block decoding: the semantic/circle/opening components cannot
read any other squeeze, and query decoding cannot read semantic or opening
answers. The rho argument is absent from Challenges and is ignored. -/
def phaseDecode
    (scalar : OracleAnswer → K) (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (queries : (Fin 8 → OracleAnswer) → Finset Fib)
    (s : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer)
    (q : Fin 8 → OracleAnswer) (_rho : OracleAnswer) : Challenges K where
  sem := fun i => scalar (s ⟨i.val, by omega⟩)
  circle := fun i => circle i (s ⟨25 + i.val, by omega⟩)
  opening := fun i => scalar (o i)
  queries := queries q

theorem phaseDecode_sem (scalar : OracleAnswer → K)
    (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (queries : (Fin 8 → OracleAnswer) → Finset Fib)
    (s s' : Fin 27 → OracleAnswer) (o o' : Fin 4 → OracleAnswer)
    (q q' : Fin 8 → OracleAnswer) (rho rho' : OracleAnswer) (i : Fin 25)
    (he : s ⟨i.val, by omega⟩ = s' ⟨i.val, by omega⟩) :
    (phaseDecode scalar circle queries s o q rho).sem i =
      (phaseDecode scalar circle queries s' o' q' rho').sem i := congrArg scalar he

theorem phaseDecode_local (scalar : OracleAnswer → K)
    (circle : Fin 2 → OracleAnswer → AspisR0.ChordGeometry.Point K)
    (queries : (Fin 8 → OracleAnswer) → Finset Fib) :
    DecodeLocal (phaseDecode scalar circle queries) where
  sem := fun _ _ _ _ _ _ _ _ _ he => congrArg scalar he
  circle := fun _ _ _ _ _ _ _ _ i he => congrArg (circle i) he
  opening := fun _ _ _ _ _ _ _ _ _ he => congrArg scalar he
  queries := fun _ _ _ _ _ _ _ => rfl

#print axioms phaseDecode_local
#print axioms R1PhaseProver.toProver
#print axioms phaseDecode
#print axioms phaseDecode_sem
end R1Z.PhaseLocalityBin
