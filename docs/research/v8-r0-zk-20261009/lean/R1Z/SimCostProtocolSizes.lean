import R1Z.SimCostAddressObstruction
import R1Z.PhaseWireLog2Bin
import R1Z.PhaseProtocolCoverageBin

/-! Protocol specialization: fixed log size, leaf widths and the surviving
adversary-address obstruction. None of these facts certifies field arithmetic
or arbitrary auxiliary metadata computation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostProtocolSizes
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.PhaseProtocolInstanceBin R1Z.SimCostIdeal
  R1Z.PhaseProtocolCoverageBin
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux) (input : HonestProver K)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x))
  (PhaseWireLog2Bin.honest input) B outputs x)

theorem query_cap : (W).qmax = 2^64 := rfl

/-- Already specialized to precisely the wire used by HeadlineV2Sim.
This remains false for every fixed choice of outputs, including protocol ones. -/
theorem protocol_sizes_impossible (L T : Nat) (s : Prepared K CommitHandle Aux) :
    ¬ ∀ adv : R1Adv K CommitHandle Aux, Sizes W L T adv s := by
  apply SimCostAddressObstruction.no_uniform_sizes
  change 0 < (2 : Nat)^64
  positivity

/-- Every selected successful ideal preparation has a nonempty transcript
prefix; its charged finish work is unbounded even at this fixed query cap. -/
theorem protocol_finish_unbounded (s : Prepared K CommitHandle Aux)
    (ht : s.table ≠ []) (bound : Nat) :
    ∃ adv : R1Adv K CommitHandle Aux, bound < (finish W adv s).2 := by
  apply SimCostAddressObstruction.finish_unbounded W _ s ht bound
  change 0 < (2 : Nat)^64
  positivity

theorem opened_c1_length (p : HonestView.Payload K R1Bat) (u : Fib) :
    (PhaseLeafEncodingBin.openedC1 p u).length = 480 := by
  unfold PhaseLeafEncodingBin.openedC1
  exact flatten_length _ (fun _ => c1_slot_length _)

theorem opened_c2_length (p : HonestView.Payload K R1Bat) (u : Fib) :
    (PhaseLeafEncodingBin.openedC2 p u).length = 128 := by
  unfold PhaseLeafEncodingBin.openedC2
  apply flatten_length (m := 32)
  intro s
  apply flatten_length (m := 16)
  intro c
  rw [List.length_take, wide_length]
  rfl

theorem view_leaf_length (v : View K CommitHandle Aux R1Bat) (T : Fin 3) (u : Fib) :
    (PhaseWireLog2Bin.viewLeaf v T u).length = if T.val = 0 then 480 else 128 := by
  unfold PhaseWireLog2Bin.viewLeaf
  split <;> (try split) <;> (try split)
  all_goals simp only [opened_c1_length, opened_c2_length, List.length_map,
    AspisR1.FoldedLeafCodec.encodeFolded_length, List.length_replicate]

/-- A protocol constant without evaluating the large finite index carrier. -/
def tableBound : Nat := TranscriptR1.schedule.length +
  2 * Fintype.card (Fin 3 ⊕ RIdx)

theorem opens_length (ch : Challenges K) :
    (PhaseWireLog2Bin.opens ch).length ≤ 2 * Fintype.card (Fin 3 ⊕ RIdx) := by
  have h0 := Finset.card_le_univ (EventsR1PBin.batchReadSet (PhaseWireLog2Bin.batchFib ch 0))
  have h1 := Finset.card_le_univ (EventsR1PBin.batchReadSet (PhaseWireLog2Bin.batchFib ch 1))
  simp only [PhaseWireLog2Bin.opens, PhaseWireLog2Bin.reads, List.length_append,
    Finset.length_toList]
  omega

theorem protocol_log_length (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : Challenges K) :
    (PhaseWireLog2Bin.log rest roots v ch).length ≤
      2 * Fintype.card (Fin 3 ⊕ RIdx) := by
  simpa only [PhaseWireLog2Bin.log, List.length_map] using opens_length ch

/-- A symbolic composition rule; no concrete random-table carrier is reduced. -/
theorem verifier_log_length {K' C A : Type} [Field K'] [Fintype K'] [DecidableEq K']
    [Algebra (ZMod AspisCircleGroupOrder.P) K']
    (wire' : R1Wire K' C A) (statement : Statement K' C)
    (v : View K' C A R1Bat) (coins : R1Coins wire'.Cm wire'.Tab) (T : Nat)
    (hc : (wire'.comLog coins.2.2.1 coins.2.1 v (drawW wire' coins)).length ≤ T) :
    (verLog wire' statement v coins).length ≤ TranscriptR1.schedule.length + T := by
  rw [verLog, List.length_append]
  have ht : (tLog wire' statement v coins).length = TranscriptR1.schedule.length :=
    List.length_map _
  rw [ht]
  exact Nat.add_le_add_left hc _

#print axioms query_cap
#print axioms protocol_sizes_impossible
#print axioms protocol_finish_unbounded
#print axioms opened_c1_length
#print axioms opened_c2_length
#print axioms view_leaf_length
#print axioms opens_length
#print axioms protocol_log_length
#print axioms verifier_log_length
end R1Z.SimCostProtocolSizes
