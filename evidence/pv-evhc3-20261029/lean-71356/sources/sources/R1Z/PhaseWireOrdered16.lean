import R1Z.PhaseWireLog2Bin
import R1Z.SerJoinOrderObstruction
import R0Z.LawTransport
/-! Order-preserving source-facing challenge carrier. No change to the legacy
set-only Challenges or assertion of a Rust instance is made here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseWireOrdered16
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.EventsR1PBin R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

/-- Projection to the old algebra retains the exact query set; source-facing
operations retain all twenty-two ordinal positions. -/
structure OrderedChallenges where
  algebra : Challenges K
  q22 : List Fib
  length_q22 : q22.length = 22
  distinct_q22 : q22.Nodup
  query_set : q22.toFinset = algebra.queries

def batchQueries (ch : OrderedChallenges) (b : Fin 2) : Finset Fib :=
  (if b.val = 0 then ch.q22.take 10 else ch.q22.drop 10).toFinset

def batchFib (ch : OrderedChallenges) (b : Fin 2) : Fin 3 → Finset Fib :=
  PhaseWireLog2Bin.treeFib (batchQueries ch b)

def fib (ch : OrderedChallenges) : Fin 3 → Finset Fib :=
  PhaseWireLog2Bin.fib ch.algebra

/-- Sorted and deduplicated per-tree indices, after the ordered 10+12 split.
The folded mapping can identify queries within one batch. -/
def indices (ch : OrderedChallenges) (b : Fin 2) (T : Fin 3) : List Fib :=
  (batchFib ch b T).sort (· ≤ ·)

def reads (ch : OrderedChallenges) (b : Fin 2) : List (Fin 3 ⊕ RIdx) :=
  (EventsR1PBin.batchReadSet (batchFib ch b)).toList

def opens (ch : OrderedChallenges) : List (Fin 3 ⊕ RIdx) :=
  reads ch 0 ++ reads ch 1

theorem batch_lengths (ch : OrderedChallenges) :
    (ch.q22.take 10).length = 10 ∧ (ch.q22.drop 10).length = 12 := by
  simp only [List.length_take, List.length_drop, ch.length_q22]
  decide

theorem query_union (ch : OrderedChallenges) :
    batchQueries ch 0 ∪ batchQueries ch 1 = ch.algebra.queries := by
  unfold batchQueries
  simp only [Fin.val_zero, Fin.val_one, ite_true, if_neg (by decide : ¬ (1 = 0))]
  rw [← List.toFinset_append, List.take_append_drop, ch.query_set]

theorem fibre_union (ch : OrderedChallenges) (T : Fin 3) :
    fib ch T = batchFib ch 0 T ∪ batchFib ch 1 T := by
  unfold fib PhaseWireLog2Bin.fib batchFib PhaseWireLog2Bin.treeFib
  split
  · rw [← Finset.image_union, query_union]
  · exact (query_union ch).symm

theorem indices_set (ch : OrderedChallenges) (b : Fin 2) (T : Fin 3) :
    (indices ch b T).toFinset = batchFib ch b T := by
  exact Finset.sort_toFinset _ _

theorem reads_nodup (ch : OrderedChallenges) (b : Fin 2) : (reads ch b).Nodup :=
  Finset.nodup_toList _

theorem reads_coverage (ch : OrderedChallenges) (b : Fin 2) (c : Fin 3 ⊕ RIdx) :
    c ∈ reads ch b ↔ openedQ (batchFib ch b) c := by
  simp only [reads, Finset.mem_toList, EventsR1PBin.mem_batchReadSet]

theorem opens_coverage (ch : OrderedChallenges) (c : Fin 3 ⊕ RIdx) :
    c ∈ opens ch ↔ openedQ (fib ch) c := by
  rw [opens, List.mem_append, reads_coverage, reads_coverage]
  have he : fib ch = fun T => batchFib ch 0 T ∪ batchFib ch 1 T :=
    funext (fibre_union ch)
  rw [he, PhaseWireLog2Bin.opened_union]

/-- D80 batch laws at the extended carrier. This cannot inhabit the legacy
RWireBatches until that interface receives the ordered challenge. -/
structure OrderedWireBatches where
  batchFib : OrderedChallenges → Fin 2 → Fin 3 → Finset Fib
  reads : OrderedChallenges → Fin 2 → List (Fin 3 ⊕ RIdx)
  concatenation : ∀ ch, opens ch = reads ch 0 ++ reads ch 1
  nodup : ∀ ch b, (reads ch b).Nodup
  coverage : ∀ ch b c, c ∈ reads ch b ↔ openedQ (batchFib ch b) c
  fibre_union : ∀ ch T, fib ch T = batchFib ch 0 T ∪ batchFib ch 1 T

def batches : OrderedWireBatches where
  batchFib := batchFib
  reads := reads
  concatenation := fun _ => rfl
  nodup := reads_nodup
  coverage := reads_coverage
  fibre_union := fibre_union

variable {CommitHandle Aux : Type}

def log (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : OrderedChallenges) :
    List (List UInt8 × OracleAnswer) :=
  (opens ch).map (PhaseWireLog2Bin.entry rest roots v)

theorem ordered_log (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : (PhaseWireLog2Bin.honest h).Instance)
    (sec : SecP) (d : OracleAnswer) (τ : Tape K F)
    (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (ch : OrderedChallenges) :
    log rest roots (view (PhaseWireLog2Bin.honest h) B outputs x w ch.algebra τ) ch =
    (opens ch).map (fun c =>
      (gram [] 0 (PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B
        (PhaseWireLog2Bin.honest h) w x τ ch.algebra) sec d rest
        (cposOf (E₁ := PrivacyR1AcctModel.E₁) (E₂ := PrivacyR1AcctModel.E₂) c),
        ansC roots rest c)) := by
  apply List.map_congr_left
  intro c hc
  exact PhaseWireLog2Bin.entry_grammar h outputs x w τ ch.algebra [] 0 sec d roots rest c
    ((opens_coverage ch c).mp hc)

/-- The simulator applies the identical public function to the retained
transcript. No witness or mask tape is an input to the batch schedule. -/
def publicSchedule {Transcript : Type} (decode : Transcript → OrderedChallenges)
    (transcript : Transcript) : List (Fin 3 ⊕ RIdx) := opens (decode transcript)

theorem simulator_schedule {Transcript : Type} (decode : Transcript → OrderedChallenges)
    (real simulator : Transcript) (same : real = simulator) :
    publicSchedule decode real = publicSchedule decode simulator :=
  congrArg (publicSchedule decode) same

/-- Deterministic public postprocessing preserves the exact distinguishing
bound of a joint transcript, including correlations with its disclosed view.
This is a law about joint views, never a marginal-hiding claim. -/
theorem public_postprocessing {R S V U : Type} [Fintype R] [Fintype S]
    (real : R → V) (ideal : S → V) (encode : V → U) (ε : ℚ)
    (hprivacy : ∀ test : V → Bool,
      |mean (fun r => bit (test (real r))) - mean (fun s => bit (test (ideal s)))| ≤ ε) :
    ∀ test : U → Bool,
      |mean (fun r => bit (test (encode (real r)))) -
       mean (fun s => bit (test (encode (ideal s))))| ≤ ε := by
  intro test
  exact hprivacy (test ∘ encode)

/-- Current-source (SPLIT=10) correction to the older split-11 witness. -/
def first : List Fib := SerJoinOrderObstruction.first
def crossed : List Fib :=
  [0,1,2,3,4,5,6,7,8,10,9,11,12,13,14,15,16,17,18,19,20,21]

theorem witnesses : first.length = 22 ∧ first.Nodup ∧
    crossed.length = 22 ∧ crossed.Nodup ∧ first.toFinset = crossed.toFinset ∧
    (first.take 10).toFinset ≠ (crossed.take 10).toFinset := by decide

theorem no_legacy_factorization (batch : Finset Fib → Finset Fib) :
    ¬ (∀ qs : List Fib, qs.length = 22 → qs.Nodup →
      batch qs.toFinset = (qs.take 10).toFinset) := by
  intro h
  have ha := h first witnesses.1 witnesses.2.1
  have hb := h crossed witnesses.2.2.1 witnesses.2.2.2.1
  rw [witnesses.2.2.2.2.1] at ha
  exact witnesses.2.2.2.2.2 (ha.symm.trans hb)

#print axioms batch_lengths
#print axioms query_union
#print axioms fibre_union
#print axioms indices_set
#print axioms reads_nodup
#print axioms reads_coverage
#print axioms opens_coverage
#print axioms batches
#print axioms ordered_log
#print axioms simulator_schedule
#print axioms public_postprocessing
#print axioms witnesses
#print axioms no_legacy_factorization
end R1Z.PhaseWireOrdered16
