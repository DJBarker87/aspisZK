import R1Z.SimCostProtocolStoredSizes
import R1Z.SimCostTruncationBudget

/-! Final additive packet. The requested deletion-only efficiency endpoint is
blocked by a false contract, even with every protocol parameter fixed. This
packet records the obstruction on the actual preparation, not a substitute
simulator or a changed adversary class. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostProtocolPacket
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.SimCostIdeal R1Z.PhaseProtocolInstanceBin
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux) (input : HonestProver K)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "h" => PhaseWireLog2Bin.honest input
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "P" => PredicateR1.P_R1 (ZkStatement.HonestProver.transport h)
  B PrivacyR1AcctBasis.packing_laws
local notation "sim" => R0Z.RefPayload.simE (ZkStatement.HonestProver.transport h) B outputs x

/-- The exact size contract requested for HeadlineV2Sim is impossible on every
fixed random input of its protocol-specialized preparation. The public output
function and field/view stages need not be varied by the counterexample. -/
theorem headline_sim_sizes_false (L T : Nat)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape K F)) :
    ¬ ∀ adv : R1Adv K CommitHandle Aux,
      Sizes W L T adv (prepare W 8 (by decide) P x sim r) := by
  exact SimCostProtocolSizes.protocol_sizes_impossible template input outputs x L T _

/-- Any certified preparation with a nonempty table inherits the actual charged
work obstruction. An assigned preparation tariff cannot repair replay costs. -/
theorem run_unbounded_of_table {K' C A : Type} [Field K'] [Fintype K'] [DecidableEq K']
    [Algebra (ZMod AspisCircleGroupOrder.P) K'] {F' : Subfield K'}
    (wire' : R1Wire K' C A) (hq : 0 < wire'.qmax) (N : Nat) (hN : 0 < N)
    (pred : Challenges K' → Prop) (statement : Statement K' C)
    (simulator : Challenges K' → Tape K' F' → View K' C A R1Bat)
    (budget : Nat) (prep : Preparation wire' N hN pred statement simulator budget)
    (r : Coins wire' N)
    (ht : (prepare wire' N hN pred statement simulator r).table ≠ [])
    (bound : Nat) :
    ∃ adv : R1Adv K' C A,
      bound < (run wire' N hN pred statement simulator budget prep adv r).2 := by
  have ht' : (prep.run r).1.table ≠ [] := by rw [prep.erase]; exact ht
  obtain ⟨adv, ha⟩ := SimCostAddressObstruction.finish_unbounded wire' hq (prep.run r).1 ht' bound
  refine ⟨adv, ?_⟩
  change bound < (prep.run r).2 + (finish wire' adv (prep.run r).1).2
  omega

#print axioms headline_sim_sizes_false
#print axioms run_unbounded_of_table
end R1Z.SimCostProtocolPacket
