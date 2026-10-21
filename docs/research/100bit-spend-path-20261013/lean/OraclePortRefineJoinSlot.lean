import OraclePortInnerOrderCounterexample

/-! Source-side accepted-run facts. Guard erasure below is unconditional;
the separate indexed frontier/level correspondence to the old recursive tree
is NOT assumed or asserted by these lemmas. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRefineJoinSlot
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortInnerOrderFrozen
attribute [local instance] Classical.propDecidable

def unguardedTail (p : Parsed) (batch kind : Nat) (live : Live) : Program Bytes State Bool :=
  verifyInPlace (OraclePortBatchDraft.committedRoot p kind) live
    ((slice p.wire (slotStart (3*batch+kind)) (32*capacity (3*batch+kind))).take
      (32*nodeCount 18 (live.map Prod.fst)))

theorem padding_guard_erasure (H : Bytes → State) (p : Parsed) (batch kind : Nat)
    (live : Live) (ha : (eval H (slotTail p batch kind live)).2 = true) :
    eval H (slotTail p batch kind live) = eval H (unguardedTail p batch kind live) := by
  unfold slotTail at ha ⊢
  dsimp only at ha ⊢
  split at ha
  · rename_i wf
    simp only [if_pos wf]
    split at ha
    · rename_i guard
      simp only [if_pos guard]
      rfl
    · simp only [eval,Bool.false_eq_true] at ha
  · simp only [eval,Bool.false_eq_true] at ha

/-- Successful leaf scans have queried every source position, in source
sorted order, including all duplicate positions. Failed scans may stop early. -/
theorem accepted_leaf_log (H : Bytes → State) (p : Parsed)
    (q : Fin 22 → Fin 262144) (kind : Nat) (ps : List Nat) (rev out : Live)
    (ha : (eval H (hashLeaves p q kind ps rev)).2 = some out) :
    (eval H (hashLeaves p q kind ps rev)).1 = ps.map (fun pos => (leaf p kind pos,H (leaf p kind pos))) := by
  induction ps generalizing rev with
  | nil => rfl
  | cons pos rest ih =>
    cases rev with
    | nil =>
      simp only [hashLeaves,eval] at ha ⊢
      rw [ih _ ha]
      rfl
    | cons entry tail =>
      rcases entry with ⟨j,v⟩
      by_cases hi : index q kind pos = j
      · by_cases hd : H (leaf p kind pos) = v
        · simp only [hashLeaves,eval,if_pos hi,if_pos hd] at ha ⊢
          rw [ih _ ha]
          rfl
        · simp only [hashLeaves,eval,if_pos hi,if_neg hd] at ha
          cases ha
      · simp only [hashLeaves,eval,if_neg hi] at ha ⊢
        rw [ih _ ha]
        rfl

/-- Generic height induction exposes exactly the successful level chain;
no height-18 recurrence is reduced. -/
theorem successful_levels (H : Bytes → State) (h : Nat) (live : Live) (nodes : Bytes)
    (last : Live × Bytes) (ha : (eval H (runLevels h live nodes)).2 = some last) :
    ∃ chain : List (Live × Bytes), chain.length = h+1 ∧
      chain.head? = some (live,nodes) ∧ chain.getLast? = some last ∧
      ∀ k (hk : k+1 < chain.length),
        (eval H (runLevel (chain[k].1.length) chain[k].1 chain[k].2)).2 = some chain[k+1] := by
  induction h generalizing live nodes with
  | zero =>
    have same : (live,nodes) = last := Option.some.inj ha
    refine ⟨[(live,nodes)],rfl,rfl,?_,?_⟩
    · simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none] using congrArg some same
    · intro k hk
      simp only [List.length_singleton] at hk
      omega
  | succ h ih =>
    rw [runLevels,eval_bind] at ha
    cases hs : (eval H (runLevel live.length live nodes)).2 with
    | none => simp only [hs,eval] at ha; cases ha
    | some next =>
      simp only [hs] at ha
      obtain ⟨chain,hlen,hhead,hlast,hsteps⟩ := ih next.1 next.2 ha
      refine ⟨(live,nodes)::chain,by simp [hlen],rfl,?_,?_⟩
      · simp only [List.getLast?_cons,hlast,Option.getD_some]
      · intro k hk
        cases k with
        | zero =>
          have first : chain[0] = next := by
            cases chain with
            | nil => simp at hhead
            | cons a rest => exact Option.some.inj hhead
          simpa only [List.getElem_cons_zero,List.getElem_cons_succ,first] using hs
        | succ k =>
          simpa only [List.getElem_cons_succ] using hsteps k (by simpa using hk)

/-- The inherited padding witness is harmless for acceptance implication:
its old helper accepts for every wire in this oracle world. This is NOT the
general frozen-slot refinement theorem. -/
theorem padding_witness_direction (wire : Bytes)
    (_ha : (eval OraclePortInnerOrderCounterexample.H
      (verifySlot_frozen ⟨wire,[]⟩ OraclePortShortCircuitSlotObstruction.zeroQueries 0 1)).2 = true) :
    (eval OraclePortInnerOrderCounterexample.H
      (OraclePortBatchDraft.verifySlot ⟨wire,[]⟩ OraclePortShortCircuitSlotObstruction.zeroQueries 0 1)).2 = true :=
  OraclePortInnerOrderCounterexample.old_accepts wire

#print axioms padding_guard_erasure
#print axioms accepted_leaf_log
#print axioms successful_levels
#print axioms padding_witness_direction
end AspisR1.OraclePortRefineJoinSlot
end
