import OraclePortRefineJoinSlot
import OraclePortInnerOrderRejectLog

/-! Accepted-slot schedule obstruction, with symbolic height induction.
This is a raw helper witness, not a full-parser reachable proof. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAccLogSlot
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OracleDecisionMultiTree
open OraclePortInnerOrderFrozen OraclePortInnerOrderCounterexample
open OraclePortShortCircuitSlotObstruction (zeroQueries spine zero_build)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] runLevels runLevel verifyInPlace slotTail verifySlot_frozen eval

def zeroWire : Bytes := List.replicate (slotStart 1 + 32*capacity 1) 0

theorem zero_slice : slice zeroWire (slotStart 1) (32*capacity 1) =
    List.replicate (32*capacity 1) 0 := by
  simp [slice,zeroWire,List.drop_replicate,List.take_replicate]

theorem levels_singleton (h : Nat) (nodes : Bytes) (hn : 32*h ≤ nodes.length) :
    (eval H (runLevels h [(0,z)] nodes)).2 = some ([(0,z)],nodes.drop (32*h)) := by
  induction h generalizing nodes with
  | zero => simp [runLevels,eval]
  | succ h ih =>
    have ht : (nodes.take 32).length = 32 := by simp; omega
    have hd : SemanticRecordCodec.decodeState (nodes.take 32) =
        some (FS2.Duplex.stateOfBytes (nodes.take 32)) := by simp [SemanticRecordCodec.decodeState,ht]
    have tail := ih (nodes.drop 32) (by simp only [List.length_drop]; omega)
    simp only [runLevels,runLevel,List.length_singleton,List.head!_nil,
      Bool.false_eq_true,if_false,hd,eval_bind,eval,H,Option.map_some,
      Nat.zero_div,tail,List.drop_drop]
    congr 3; omega

theorem frozen_accepts_zero :
    (eval H (verifySlot_frozen ⟨zeroWire,[]⟩ zeroQueries 0 1)).2 = true := by
  have wf : wellFormed ([0] : List Nat) := by
    simp [wellFormed]
  have cap : 18 ≤ capacity 1 := by decide
  have tail : (slice zeroWire (slotStart 1) (32*capacity 1)).take (32*18) =
      List.replicate (32*18) 0 := by
    rw [zero_slice,List.take_replicate,Nat.min_eq_left (by omega)]
  have guard : (slice zeroWire (slotStart 1) (32*capacity 1)).drop (32*18) =
      List.replicate (32*(capacity 1-18)) 0 := by
    rw [zero_slice,List.drop_replicate]
    congr 1 <;> omega
  have lev := levels_singleton 18 (List.replicate (32*18) 0) (by rw [List.length_replicate])
  simp only [List.drop_replicate,Nat.sub_self] at lev
  simp only [verifySlot_frozen,eval_bind,hash_zero]
  change (eval H (slotTail ⟨zeroWire,[]⟩ 0 1 [(0,z)])).2 = true
  unfold slotTail
  simp only [List.map_cons,List.map_nil,if_pos wf,count_singleton_zero,
    show 3*0+1=1 by decide]
  rw [if_pos ⟨cap,by rw [zero_slice,List.length_replicate],guard⟩,tail]
  unfold verifyInPlace
  rw [if_pos ⟨wf,by rw [List.length_replicate]⟩]
  simp only [eval_bind,lev]
  have root : OraclePortBatchDraft.committedRoot ⟨zeroWire,[]⟩ 1 = z := rfl
  rw [root]
  simp only [eval,List.replicate_zero,eq_self,and_self,decide_true,true_and]

theorem model_first_two (p : Parsed) :
    ∃ parent rest, (eval H (OraclePortBatchDraft.verifySlot p zeroQueries 0 1)).1 =
      (leaf p 1 0,z) :: (BinMerkle32Path.nodeInput parent,z) :: rest := by
  have shape := zero_build (selected zeroQueries 0 1) (input p zeroQueries 0 1)
    (sibling p zeroQueries 0 1)
    (by rw [selected_zero_one]; simp)
    (by rw [selected_zero_one]; intro i hi; simpa using hi) 18
  rw [input_zero_one] at shape
  obtain ⟨rest,eq⟩ := OraclePortShortCircuitSlotObstruction.spine_first_two
    (leaf p 1 0) (fun k => sibling p zeroQueries 0 1 k (2^k)) H 17
  rw [← shape] at eq
  simp only [OraclePortBatchDraft.verifySlot,tree,eval_bind,eval,List.append_nil]
  rw [eq]
  exact ⟨_,_,rfl⟩

theorem accepted_slot_logs_differ :
    (eval H (verifySlot_frozen ⟨zeroWire,[]⟩ zeroQueries 0 1)).2 = true ∧
    (eval H (OraclePortBatchDraft.verifySlot ⟨zeroWire,[]⟩ zeroQueries 0 1)).2 = true ∧
    (eval H (verifySlot_frozen ⟨zeroWire,[]⟩ zeroQueries 0 1)).1 ≠
      (eval H (OraclePortBatchDraft.verifySlot ⟨zeroWire,[]⟩ zeroQueries 0 1)).1 := by
  refine ⟨frozen_accepts_zero,old_accepts zeroWire,?_⟩
  intro eq
  obtain ⟨parent,rest,hm⟩ := model_first_two ⟨zeroWire,[]⟩
  have hl := OraclePortInnerOrderRejectLog.leaf_log ⟨zeroWire,[]⟩
  simp only [verifySlot_frozen,eval_bind,hash_zero,hl] at eq
  rw [hm] at eq
  have second := congrArg (fun xs => (xs[1]?).map (fun x => x.1.head?)) eq
  simp only [show List.range 10 = 0 :: 1 :: List.range' 2 8 from rfl,
    List.map_cons,List.cons_append,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.map_some,leaf,BinMerkle32Leaf.leafInput,BinMerkle32Path.nodeInput,
    show ¬ (1 : Nat) = 0 by decide,if_false,if_true,List.head?_cons] at second
  contradiction

#print axioms zero_slice
#print axioms levels_singleton
#print axioms frozen_accepts_zero
#print axioms model_first_two
#print axioms accepted_slot_logs_differ
end AspisR1.OraclePortAccLogSlot
end
