import R1Z.SimCostProtocolSizes

/-! Bounds on the protocol's own programmed table, independently of the
unbounded adversary addresses. These close two of the three Sizes conjuncts;
they do not assert the false third conjunct. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostProtocolStoredSizes
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.SimCostIdeal R1Z.SimCostReplay R1Z.TranscriptR1
  R1Z.PhaseProtocolInstanceBin R1Z.PhaseProtocolCoverageBin R1Z.SimCostProtocolSizes
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
variable {CommitHandle Aux : Type}

theorem entry_length (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (c : Fin 3 ⊕ RIdx) :
    (PhaseWireLog2Bin.entry rest roots v c).1.length ≤ 514 := by
  rcases c with T | (b | i | ⟨T,u⟩ | ⟨T,u⟩ | ⟨T,n⟩)
  all_goals simp only [PhaseWireLog2Bin.entry, LayoutR1PBin.nodeBytes_length,
    List.length_append, List.length_cons, List.length_nil, LensR1.length_ans]
  all_goals try omega
  rw [view_leaf_length]
  split <;> omega

theorem protocol_log_keys (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : Challenges K) :
    KeysBound 514 (PhaseWireLog2Bin.log rest roots v ch) := by
  intro a ans ha
  obtain ⟨c, _, he⟩ := List.mem_map.mp ha
  have hl := entry_length rest roots v c
  rw [he] at hl
  exact hl

theorem transcript_address_length (pub : List UInt8) (tag : UInt8)
    (v : View K CommitHandle Aux R1Bat) (c2 cf : OracleAnswer) (j : TRead) (ans : OracleAnswer) :
    (addrWith j ans (WireLengthsR1PBin.rest (transcriptWire pub tag v c2 cf))).length ≤
      RomGrammarBin.bound pub.length := by
  have hh := RomGrammarBin.transcript_length pub.length
    (SharedGrammarBridgeBin.toShared (transcriptWire pub tag v c2 cf))
    (show (SharedGrammarBridgeBin.toShared (transcriptWire pub tag v c2 cf)).publicBytes.length
        ≤ pub.length from Nat.le_refl _) j ans
  rw [SharedGrammarBridgeBin.wire_roundtrip] at hh
  exact hh

variable (template : R1Wire K CommitHandle Aux) (input : HonestProver K)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x))
    (PhaseWireLog2Bin.honest input) B outputs x)

theorem concrete_log_length (v : View K CommitHandle Aux R1Bat)
    (c : R1Coins (W).Cm (W).Tab) :
    (verLog W x v c).length ≤ TranscriptR1.schedule.length + 2 * Fintype.card (Fin 3 ⊕ RIdx) := by
  exact verifier_log_length W x v c (2 * Fintype.card (Fin 3 ⊕ RIdx))
    (protocol_log_length _ _ v _)

theorem transcript_keys (v : View K CommitHandle Aux R1Bat)
    (c : R1Coins (W).Cm (W).Tab) :
    KeysBound (RomGrammarBin.bound (R1Wire.pubBytes base x).length) (tLog W x v c) := by
  intro a ans ha
  obtain ⟨j, _, he⟩ := List.mem_map.mp ha
  have hl : (addr j (recP W x v c.1 c.2.1)).length ≤
      RomGrammarBin.bound (R1Wire.pubBytes base x).length := by
    unfold addr
    rw [transcript_rest]
    exact transcript_address_length _ _ v _ _ j _
  have he' := congrArg Prod.fst he
  dsimp only at he'
  rw [he'] at hl
  exact hl

theorem concrete_log_keys (v : View K CommitHandle Aux R1Bat)
    (c : R1Coins (W).Cm (W).Tab) :
    KeysBound (RomGrammarBin.bound (R1Wire.pubBytes base x).length) (verLog W x v c) := by
  intro a ans ha
  have hm : (a,ans) ∈ tLog W x v c ∨
      (a,ans) ∈ PhaseWireLog2Bin.log _ _ v (drawW W c) := List.mem_append.mp ha
  rcases hm with hm | hm
  · exact transcript_keys template input outputs x v c a ans hm
  · have hk := protocol_log_keys _ _ v (drawW W c) a ans hm
    exact hk.trans (by unfold RomGrammarBin.bound; omega)

/-- The protocol's stored-table contracts hold for every ideal random input,
including total retry failure. No adversary address bound is included. -/
theorem preparation_stored_sizes (P : Challenges K → Prop)
    [DecidablePred P]
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape K F)) :
    (prepare W 8 (by decide) P x sim r).table.length ≤ TranscriptR1.schedule.length + 2 * Fintype.card (Fin 3 ⊕ RIdx) ∧
    KeysBound (RomGrammarBin.bound (R1Wire.pubBytes base x).length)
      (prepare W 8 (by decide) P x sim r).table := by
  unfold prepare
  cases he : firstGood (fun c => P (drawW W c)) r.1 with
  | none =>
    constructor
    · exact Nat.zero_le _
    · intro a ans ha
      exact False.elim (List.not_mem_nil ha)
  | some k =>
    exact ⟨concrete_log_length template input outputs x _ _,
      concrete_log_keys template input outputs x _ _⟩

#print axioms entry_length
#print axioms protocol_log_keys
#print axioms transcript_address_length
#print axioms concrete_log_length
#print axioms transcript_keys
#print axioms concrete_log_keys
#print axioms preparation_stored_sizes
end R1Z.SimCostProtocolStoredSizes
