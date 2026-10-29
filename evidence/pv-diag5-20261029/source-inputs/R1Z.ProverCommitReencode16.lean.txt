import R1Z.ProverCommitFixedEndpoint
import R1Z.PhaseWireOrdered16
/-! Public reindexing and adaptive-observer transport. The transformed games
are constructed models, not a concrete Rust serialization certificate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReencode16
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkS R1Z.Batched
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable

/-- Select a logical read's bytes/answer from a previous encoding. -/
def fetch {C V : Type} [DecidableEq C] : List C → List V → C → Option V
  | a::tail, v::vs, c => if a = c then some v else fetch tail vs c
  | _, _, _ => none

theorem fetch_map {C V : Type} [DecidableEq C] (old : List C) (f : C → V)
    (c : C) (hc : c ∈ old) : fetch old (old.map f) c = some (f c) := by
  induction old with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons a old ih =>
    simp only [List.map_cons, fetch]
    by_cases ha : a = c
    · subst a; simp only [if_true]
    · rw [if_neg ha]
      apply ih
      rcases List.mem_cons.mp hc with he | he
      · exact False.elim (ha he.symm)
      · exact he

local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
abbrev Entry := List UInt8 × OracleAnswer

def reindex (ch : PhaseWireOrdered16.OrderedChallenges) (entries : List Entry) : List Entry :=
  (PhaseWireOrdered16.opens ch).map (fun c =>
    (fetch (PhaseWireLog2Bin.opens ch.algebra) entries c).getD ([], 0))

/-- The complete new ordered log, with its new multiplicities, is reconstructed
from the old log without any extra oracle query or private tape input. -/
theorem reindex_map (ch : PhaseWireOrdered16.OrderedChallenges)
    (entry : Fin 3 ⊕ RIdx → Entry) :
    reindex ch ((PhaseWireLog2Bin.opens ch.algebra).map entry) =
      (PhaseWireOrdered16.opens ch).map entry := by
  apply List.map_congr_left
  intro c hc
  have hold : c ∈ PhaseWireLog2Bin.opens ch.algebra :=
    (PhaseWireLog2Bin.opens_coverage ch.algebra c).mpr
      ((PhaseWireOrdered16.opens_coverage ch c).mp hc)
  rw [fetch_map _ entry c hold]
  rfl

/-- Recover the retained QueryScan order solely from public transcript entries.
Validation also makes malformed/rejected inputs explicit. This is a total
model decoder; source alignment of the transcript prefix is still required. -/
def recover {CommitHandle Aux : Type} (v : View K CommitHandle Aux R1Bat)
    (log : List Entry) : Option PhaseWireOrdered16.OrderedChallenges :=
  let q : Fin 8 → OracleAnswer := fun k =>
    (log[TranscriptR1.schedule.idxOf (.qb k)]?).getD ([], 0) |>.2
  let order := ((PhaseSamplerParserBin.scanned
    (PhaseQueryScanBin.stop PhaseSamplerParserBin.done q) q).1.accepted).map PhaseSamplerParserBin.fibre
  if hl : order.length = 22 then
    if hn : order.Nodup then
      if hs : order.toFinset = v.1.challenges.queries then
        some ⟨v.1.challenges, order, hl, hn, hs⟩
      else none
    else none
  else none

def encode {CommitHandle Aux : Type} (v : View K CommitHandle Aux R1Bat)
    (log : List Entry) : List Entry :=
  match recover v log with
  | none => log
  | some ch =>
    let transcriptLength := TranscriptR1.schedule.length
    let openingLength := (PhaseWireLog2Bin.opens ch.algebra).length
    log.take transcriptLength ++ reindex ch ((log.drop transcriptLength).take openingLength) ++
      log.drop (transcriptLength + openingLength)

theorem recover_algebra {CommitHandle Aux : Type}
    (v : View K CommitHandle Aux R1Bat) (log : List Entry)
    (ch : PhaseWireOrdered16.OrderedChallenges) (hr : recover v log = some ch) :
    ch.algebra = v.1.challenges := by
  unfold recover at hr
  dsimp only at hr
  split at hr
  · split at hr
    · split at hr
      · cases Option.some.inj hr
        rfl
      · cases hr
    · cases hr
  · cases hr

/-- Exact prefix/suffix transport at a validated public parse. In particular
reindexing neither changes nor discards an observer's later oracle queries. -/
theorem encode_parts {CommitHandle Aux : Type}
    (v : View K CommitHandle Aux R1Bat) (ch : PhaseWireOrdered16.OrderedChallenges)
    (front suffix : List Entry) (entry : Fin 3 ⊕ RIdx → Entry)
    (width : front.length = TranscriptR1.schedule.length)
    (parsed : recover v (front ++ (PhaseWireLog2Bin.opens ch.algebra).map entry ++ suffix) = some ch) :
    encode v (front ++ (PhaseWireLog2Bin.opens ch.algebra).map entry ++ suffix) =
      front ++ (PhaseWireOrdered16.opens ch).map entry ++ suffix := by
  unfold encode
  rw [parsed]
  simp [← width, List.take_append, List.drop_append, reindex_map]

section Transport
variable {CommitHandle Aux : Type}

def mapView (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
    (v : ROMView K CommitHandle Aux R1Bat) : ROMView K CommitHandle Aux R1Bat :=
  ⟨v.disclosed, encoding v.disclosed v.observerOracle⟩

def observer (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
    (adv : R1Adv K CommitHandle Aux) : R1Adv K CommitHandle Aux where
  prog := fun v log => adv.prog v (encoding v log)
  decide := fun v => adv.decide (mapView encoding v)

variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (N : Nat) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
local notation "model" => fsR1P W Pr N hN P Vp

def experiment (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry) :
    FSExperiments K CommitHandle Aux R1Bat F where
  Adversary := R1Adv K CommitHandle Aux
  RealRand := (model).RealRand
  IdealRand := (model).IdealRand
  real := fun h packing outputs adv x w r =>
    mapView encoding ((model).real h packing outputs (observer encoding adv) x w r)
  ideal := fun sim adv x r => mapView encoding ((model).ideal sim (observer encoding adv) x r)
  observe := fun adv v => adv.decide v

variable (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
instance real_finite : Fintype (experiment W Pr N hN P Vp encoding).RealRand :=
  inferInstanceAs (Fintype (model).RealRand)
instance real_nonempty : Nonempty (experiment W Pr N hN P Vp encoding).RealRand :=
  inferInstanceAs (Nonempty (model).RealRand)
instance ideal_finite : Fintype (experiment W Pr N hN P Vp encoding).IdealRand :=
  inferInstanceAs (Fintype (model).IdealRand)
instance ideal_nonempty : Nonempty (experiment W Pr N hN P Vp encoding).IdealRand :=
  inferInstanceAs (Nonempty (model).IdealRand)

/-- Adaptive programs receive the reencoded prefix before querying. Both games
and the final decision are transported together, with exactly the same ε. -/
theorem privacy_transport (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat) (ε : ℚ)
    (private_model : ZK_FSS h B outputs model x sim ε) :
    ZK_FSS h B outputs (experiment W Pr N hN P Vp encoding) x sim ε := by
  intro adv w hw
  exact private_model (observer encoding adv) w hw
end Transport

#print axioms fetch_map
#print axioms reindex_map
#print axioms recover_algebra
#print axioms encode_parts
#print axioms privacy_transport
end R1Z.ProverCommitReencode16
