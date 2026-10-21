import OraclePortInnerOrderCounterexample

/-! Exact rejection log of the compiled padding counterexample. This audits
one rejecting input, not the requested all-input verifier budget. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortInnerOrderRejectLog
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft
open OraclePortInnerOrderFrozen OraclePortInnerOrderCounterexample
open OraclePortShortCircuitSlotObstruction (zeroQueries)
attribute [local instance] Classical.propDecidable

theorem tail_log (p : Parsed) (ps : List Nat) :
    (eval H (hashLeaves p zeroQueries 1 ps [(0,z)])).1 =
      ps.map (fun pos => (leaf p 1 pos,z)) := by
  induction ps with
  | nil => rfl
  | cons pos rest ih =>
    simpa only [hashLeaves,eval,index,zeroQueries,Fin.val_zero,
      show ¬ (1 : Nat) = 2 by decide,if_false,show (0 : Nat) = 0 from rfl,
      if_true,H,List.map_cons] using congrArg (List.cons (leaf p 1 pos,z)) ih

theorem leaf_log (p : Parsed) :
    (eval H (hashLeaves p zeroQueries 1 (sortedPositions zeroQueries 0 1) [])).1 =
      (List.range 10).map (fun pos => (leaf p 1 pos,z)) := by
  rw [sorted_zero_one]
  change (eval H (hashLeaves p zeroQueries 1 (0 :: List.range' 1 9) [])).1 = _
  simp only [hashLeaves,eval,H,index,zeroQueries,Fin.val_zero,
    show ¬ (1 : Nat) = 2 by decide,if_false]
  rw [tail_log]
  rfl

theorem padding_stops : slotTail ⟨badWire,[]⟩ 0 1 [(0,z)] = .done false := by
  unfold slotTail
  simp only [List.map_cons,List.map_nil]
  split
  · rw [count_singleton_zero]
    have bad : ¬ ((slice badWire (slotStart 1) (32*capacity 1)).drop (32*18) =
        List.replicate (32*(capacity 1-18)) 0) := by
      rw [bad_slot,List.drop_replicate]
      intro he
      have hh := congrArg List.head? he
      change some (1 : AspisV8R19.DuplexFrames.Byte) = some 0 at hh
      contradiction
    simp only [show 3*0+1=1 by decide,bad,and_false,if_false]
  · rfl

/-- Every leaf is issued in sorted source order, then padding stops all parents. -/
theorem rejecting_log :
    eval H (verifySlot_frozen ⟨badWire,[]⟩ zeroQueries 0 1) =
      ((List.range 10).map (fun pos => (leaf ⟨badWire,[]⟩ 1 pos,z)),false) := by
  simp only [verifySlot_frozen,eval_bind,hash_zero,leaf_log,padding_stops,eval,
    List.append_nil]

theorem rejecting_log_length :
    (eval H (verifySlot_frozen ⟨badWire,[]⟩ zeroQueries 0 1)).1.length = 10 := by
  rw [rejecting_log]
  simp

theorem rejecting_log_budget :
    (eval H (verifySlot_frozen ⟨badWire,[]⟩ zeroQueries 0 1)).1.length ≤ 1161 := by
  rw [rejecting_log_length]
  decide

#print axioms tail_log
#print axioms leaf_log
#print axioms padding_stops
#print axioms rejecting_log
#print axioms rejecting_log_length
#print axioms rejecting_log_budget
end AspisR1.OraclePortInnerOrderRejectLog
end
