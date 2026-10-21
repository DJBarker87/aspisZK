import R1Z.SimCostRelativeReplay
import R1Z.SimCostProtocolStoredSizes

/-! Exact ideal-game relative-cost composition. Protocol table-size and
stored-key contracts are discharged. Preparation remains a separate certified
stage; no arbitrary callback receives a fabricated constant-time tariff. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostRelativeIdeal
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.SimCostIdeal R1Z.SimCostReplay R1Z.SimCostRelativeReplay
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The adaptive-path input length, evaluated using precisely the published
view, programmed table and fallback of the reference ideal experiment. -/
def adversaryInput (W : R1Wire K CommitHandle Aux)
    (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) : Nat :=
  inputLength (fun a => (s.table.lookup a).getD (s.fallback a))
    (adv.prog s.view s.table) W.qmax

def relativeCoefficient (C L T : Nat) : Nat := C+(T+1)*(L+6)+3*T+1

theorem finish_relative (W : R1Wire K CommitHandle Aux)
    (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) (L T : Nat)
    (hlen : s.table.length ≤ T) (hkeys : KeysBound L s.table) :
    (finish W adv s).2 ≤ relativeCoefficient 0 L T * (adversaryInput W adv s + 1) := by
  have hb := replay_relative s.table s.fallback (adv.prog s.view s.table) W.qmax L hkeys
  have hc : (s.table.length+1)*(L+6) ≤ (T+1)*(L+6) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 1)
  have hm := Nat.mul_le_mul_right (adversaryInput W adv s) hc
  change 2*s.table.length + (replay _ _ _ _).2 + s.table.length+1 ≤ _
  change (replay _ _ _ _).2 ≤ (s.table.length+1)*(L+6)*adversaryInput W adv s at hb
  unfold relativeCoefficient
  nlinarith

theorem run_relative (W : R1Wire K CommitHandle Aux) (N : Nat) (hN : 0 < N)
    (P : Challenges K → Prop) (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (C L T : Nat) (prep : Preparation W N hN P x sim C)
    (adv : R1Adv K CommitHandle Aux) (r : Coins (F := F) W N)
    (hs : (prepare W N hN P x sim r).table.length ≤ T ∧
      KeysBound L (prepare W N hN P x sim r).table) :
    (run W N hN P x sim C prep adv r).2 ≤ relativeCoefficient C L T *
      (adversaryInput W adv (prepare W N hN P x sim r) + 1)^1 := by
  have hb := prep.bound r
  have ht := finish_relative W adv (prepare W N hN P x sim r) L T hs.1 hs.2
  change (prep.run r).2 + (finish W adv (prep.run r).1).2 ≤ _
  rw [prep.erase]
  simp only [pow_one]
  unfold relativeCoefficient at ht ⊢
  nlinarith

section Protocol
local notation "KP" => PrivacyR1AcctBasis.K
local notation "FP" => PrivacyR1AcctBasis.F
local notation "BP" => PrivacyR1AcctBasis.basis
variable (template : R1Wire KP CommitHandle Aux) (input : HonestProver KP)
  (outputs : Statement KP CommitHandle → Challenges KP → Aux)
  (x : Statement KP CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire
  (PhaseProtocolInstanceBin.wire base (List.length (R1Wire.pubBytes base x))
    (PhaseWireLog2Bin.honest input) BP outputs x)

/-- Unconditional protocol-instance replay theorem. Preparation is the actual
reference value, not a hypothesis on adversary addresses. -/
theorem protocol_finish_relative (P : Challenges KP → Prop)
    (sim : Challenges KP → Tape KP FP → View KP CommitHandle Aux R1Bat)
    (adv : R1Adv KP CommitHandle Aux)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape KP FP)) :
    (finish W adv (prepare W 8 (by decide) P x sim r)).2 ≤
      relativeCoefficient 0 (RomGrammarBin.bound (R1Wire.pubBytes base x).length)
        (TranscriptR1.schedule.length + 2 * Fintype.card (Fin 3 ⊕ RIdx)) *
      (adversaryInput W adv (prepare W 8 (by decide) P x sim r) + 1)^1 := by
  have hs := SimCostProtocolStoredSizes.preparation_stored_sizes template input outputs x P sim r
  simpa only [pow_one] using finish_relative W adv _ _ _ hs.1 hs.2

/-- All size contracts are proved at the protocol. The only additional cost
premise is a certified deterministic implementation of preparation. The
binary-randomness refinement is a further statistical obligation. -/
theorem protocol_run_relative (P : Challenges KP → Prop)
    (sim : Challenges KP → Tape KP FP → View KP CommitHandle Aux R1Bat)
    (C : Nat) (prep : Preparation W 8 (by decide) P x sim C)
    (adv : R1Adv KP CommitHandle Aux)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape KP FP)) :
    (run W 8 (by decide) P x sim C prep adv r).2 ≤
      relativeCoefficient C (RomGrammarBin.bound (R1Wire.pubBytes base x).length)
        (TranscriptR1.schedule.length + 2 * Fintype.card (Fin 3 ⊕ RIdx)) *
      (adversaryInput W adv (prepare W 8 (by decide) P x sim r) + 1)^1 := by
  exact run_relative W 8 (by decide) P x sim C _ _ prep adv r
    (SimCostProtocolStoredSizes.preparation_stored_sizes template input outputs x P sim r)
end Protocol

#print axioms finish_relative
#print axioms run_relative
#print axioms protocol_finish_relative
#print axioms protocol_run_relative
end R1Z.SimCostRelativeIdeal
