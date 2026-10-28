import NDO_JGr_Keys
import JGk_TX2_LeafPush
import JGk_TX2_KeyInjective
import NDO_JGr_Counts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Keys
open Aeneas Aeneas.Std Result MultiproofConeRef

def positions : List Nat := [6,0,1,9,7,5,8,4,2,3]
def keys (kind : Nat) : Array U64 16#usize := Classical.choose (JGr_Keys.source kind)
theorem returned (kind : Nat) : Port4B_Install.leaves.op5 (JGr_Keys.raw kind) 10#usize=ok (keys kind) :=
  (Classical.choose_spec (JGr_Keys.source kind)).1
#print axioms returned

theorem sorted0 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 0=positions := by
  let key := OraclePortSelectedDraft.index JGr_Keys.q 0
  have raw : (OraclePortSelectedDraft.batchPositions 0).map key=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813] := rfl
  have distinct : ∀ a∈OraclePortSelectedDraft.batchPositions 0, ∀ b∈OraclePortSelectedDraft.batchPositions 0, key a=key b → a=b := by
    apply List.inj_on_of_nodup_map
    rw [raw]
    decide
  have permutation : [93499,147529,216823,245899,209371,192317,65593,183859,193093,159813].Perm JGr_Count0.indices00 := by
    apply Multiset.coe_eq_coe.mp
    simp only [JGr_Count0.indices00,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero]
    ac_rfl
  have ordered : JGr_Count0.indices00.Pairwise (·≤·) := by decide
  have mapped : (OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 0).map key=JGr_Count0.indices00 := by
    apply JGk_TX2_ComparatorTransport.key_stream (OraclePortSelectedDraft.batchPositions 0) key _ JGr_Count0.indices00
    · intro a ha b hb
      apply decide_eq_decide.mpr
      have h := JGk_TX2_ComparatorTransport.tie_transport (OraclePortSelectedDraft.batchPositions 0) key
        (fun a b => a≤b) distinct (fun _ _ => Nat.le_refl _) a ha b hb
      exact decide_eq_decide.mp h
    · rw [raw]
      exact permutation
    · exact ordered
  apply JGk_TX2_KeyInjective.source (OraclePortSelectedDraft.batchPositions 0) _ _ key distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · intro a ha
    simp only [positions,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · exact mapped.trans (show positions.map key=JGr_Count0.indices00 from rfl).symm
#print axioms sorted0
theorem sorted1 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 1=positions := by
  let key := OraclePortSelectedDraft.index JGr_Keys.q 1
  have raw : (OraclePortSelectedDraft.batchPositions 0).map key=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813] := rfl
  have distinct : ∀ a∈OraclePortSelectedDraft.batchPositions 0, ∀ b∈OraclePortSelectedDraft.batchPositions 0, key a=key b → a=b := by
    apply List.inj_on_of_nodup_map
    rw [raw]
    decide
  have permutation : [93499,147529,216823,245899,209371,192317,65593,183859,193093,159813].Perm JGr_Count0.indices00 := by
    apply Multiset.coe_eq_coe.mp
    simp only [JGr_Count0.indices00,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero]
    ac_rfl
  have ordered : JGr_Count0.indices00.Pairwise (·≤·) := by decide
  have mapped : (OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 1).map key=JGr_Count0.indices00 := by
    apply JGk_TX2_ComparatorTransport.key_stream (OraclePortSelectedDraft.batchPositions 0) key _ JGr_Count0.indices00
    · intro a ha b hb
      apply decide_eq_decide.mpr
      have h := JGk_TX2_ComparatorTransport.tie_transport (OraclePortSelectedDraft.batchPositions 0) key
        (fun a b => a≤b) distinct (fun _ _ => Nat.le_refl _) a ha b hb
      exact decide_eq_decide.mp h
    · rw [raw]
      exact permutation
    · exact ordered
  apply JGk_TX2_KeyInjective.source (OraclePortSelectedDraft.batchPositions 0) _ _ key distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · intro a ha
    simp only [positions,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · exact mapped.trans (show positions.map key=JGr_Count0.indices00 from rfl).symm
#print axioms sorted1
theorem sorted2 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 2=positions := by
  let key := OraclePortSelectedDraft.index JGr_Keys.q 2
  have raw : (OraclePortSelectedDraft.batchPositions 0).map key=[23374,36882,54205,61474,52342,48079,16398,45964,48273,39953] := rfl
  have distinct : ∀ a∈OraclePortSelectedDraft.batchPositions 0, ∀ b∈OraclePortSelectedDraft.batchPositions 0, key a=key b → a=b := by
    apply List.inj_on_of_nodup_map
    rw [raw]
    decide
  have permutation : [23374,36882,54205,61474,52342,48079,16398,45964,48273,39953].Perm JGr_Count2.indices00 := by
    apply Multiset.coe_eq_coe.mp
    simp only [JGr_Count2.indices00,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero]
    ac_rfl
  have ordered : JGr_Count2.indices00.Pairwise (·≤·) := by decide
  have mapped : (OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 2).map key=JGr_Count2.indices00 := by
    apply JGk_TX2_ComparatorTransport.key_stream (OraclePortSelectedDraft.batchPositions 0) key _ JGr_Count2.indices00
    · intro a ha b hb
      apply decide_eq_decide.mpr
      have h := JGk_TX2_ComparatorTransport.tie_transport (OraclePortSelectedDraft.batchPositions 0) key
        (fun a b => a≤b) distinct (fun _ _ => Nat.le_refl _) a ha b hb
      exact decide_eq_decide.mp h
    · rw [raw]
      exact permutation
    · exact ordered
  apply JGk_TX2_KeyInjective.source (OraclePortSelectedDraft.batchPositions 0) _ _ key distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · intro a ha
    simp only [positions,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · exact mapped.trans (show positions.map key=JGr_Count2.indices00 from rfl).symm
#print axioms sorted2

theorem stream0 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 0 (keys 0) 0#usize positions := by
  rw [←sorted0]
  exact (Classical.choose_spec (JGr_Keys.source 0)).2
#print axioms stream0
theorem stream1 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 1 (keys 1) 0#usize positions := by
  rw [←sorted1]
  exact (Classical.choose_spec (JGr_Keys.source 1)).2
#print axioms stream1
theorem stream2 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 2 (keys 2) 0#usize positions := by
  rw [←sorted2]
  exact (Classical.choose_spec (JGr_Keys.source 2)).2
#print axioms stream2
end AspisR1.JGu_Keys
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Keys
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem advance_loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (kind slot pos next : Usize) (s t : reference.Scratch)
    (body : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) D
      JFx_NativeBytes.proof root kind hash 0#usize 10#usize slot (keys kind.val)
      s.idx s.val s.n pos=ok (.cont (t.idx,t.val,t.n,next))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) D
      JFx_NativeBytes.proof root kind s.idx s.val hash 0#usize 10#usize slot (keys kind.val) s.n pos=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) D
      JFx_NativeBytes.proof root kind t.idx t.val hash 0#usize 10#usize slot (keys kind.val) t.n next := by
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,body,bind_tc_ok]
  rfl
#print axioms advance_loop
end AspisR1.JGu_Keys
end
