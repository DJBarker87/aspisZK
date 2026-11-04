import R1Z.GamesR1PBin
import R1Z.RomFiniteBin

/-! A whole-run event covering every repeated read is not a birthday event.
The retained post-proof adversary may deliberately query one address twice.
The counterexample uses in-domain reads and works for every oracle and every
honest outcome, including failure. No property of the scan is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanWholeRunRepeatObstruction
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.GamesR1 R1Z.GamesR1PBin
attribute [local instance] Classical.propDecidable

/-- Two reads, using the answer-insensitive continuations allowed by OProg. -/
def repeatProgram (a : List UInt8) : OProg :=
  .query a (fun _ => .query a (fun _ => .done))

/-- The concrete fixed log event: some address occurs more than once. -/
def repeatedRead (log : List (List UInt8 × OracleAnswer)) : Prop :=
  ¬ (log.map Prod.fst).Nodup

theorem repeatProgram_log (a : List UInt8) (H : List UInt8 → OracleAnswer)
    (q : ℕ) (hq : 2 ≤ q) :
    runLog (repeatProgram a) H q = [(a, H a), (a, H a)] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [show 2 + n = n + 1 + 1 by omega]
  rfl

theorem prefix_repeat (pre : List (List UInt8 × OracleAnswer))
    (a : List UInt8) (b : OracleAnswer) :
    repeatedRead (pre ++ [(a, b), (a, b)]) := by
  simp [repeatedRead, List.nodup_append]

variable {K CommitHandle Aux : Type} [Field K]

def repeatAdversary (a : List UInt8) : R1Adv K CommitHandle Aux where
  prog := fun _ _ => repeatProgram a
  decide := fun _ => false

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Exact retained real game: the repeated reads survive both firstGood branches.
Thus they are also reads of the complete run, not just of an invented subrun. -/
theorem real_game_repeats (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (N : ℕ)
    (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (r : W.Tab × (Fin N → SecP)) (a : List UInt8) (hq : 2 ≤ W.qmax) :
    repeatedRead (realGameP W Pr N P Vp h B outputs (repeatAdversary a) x w r).observerOracle := by
  unfold realGameP
  dsimp only
  split
  · change repeatedRead (runLog (repeatProgram a) (W.look r.1) W.qmax)
    rw [repeatProgram_log a _ _ hq]
    exact prefix_repeat [] a _
  · change repeatedRead (_ ++ runLog (repeatProgram a) (W.look r.1) W.qmax)
    rw [repeatProgram_log a _ _ hq]
    exact prefix_repeat _ a _

/-- Any excluded event containing this fixed repeated-read event has mass one.
The containment premise has only execution content, with no probability law. -/
theorem covering_event_mass_one {R : Type} [Fintype R] [Nonempty R]
    (log : R → List (List UInt8 × OracleAnswer)) (E : R → Prop)
    (hrep : ∀ r, repeatedRead (log r))
    (hcover : ∀ r, repeatedRead (log r) → E r) : eventMass E = 1 := by
  have he : ∀ r, E r := fun r => hcover r (hrep r)
  unfold eventMass
  simp only [he, if_true]
  exact mean_const 1

/-- No collision term below one bounds an event covering all repeated reads. -/
theorem no_small_covering_event {R : Type} [Fintype R] [Nonempty R]
    (log : R → List (List UInt8 × OracleAnswer)) (E : R → Prop)
    (hrep : ∀ r, repeatedRead (log r))
    (hcover : ∀ r, repeatedRead (log r) → E r)
    (κ : ℚ) (hκ : κ < 1) : ¬ eventMass E ≤ κ := by
  rw [covering_event_mass_one log E hrep hcover]
  exact not_le_of_gt hκ

#print axioms repeatProgram_log
#print axioms prefix_repeat
#print axioms real_game_repeats
#print axioms covering_event_mass_one
#print axioms no_small_covering_event
end R1Z.QueryScanWholeRunRepeatObstruction
