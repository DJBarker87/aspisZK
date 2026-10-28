import NCE_KeyReadCuts
import NCE_SortCarrierCuts

set_option autoImplicit false
namespace AspisR1.NCE_KeysCarrierJoin
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyCuts NCE_KeyProducerCuts NCE_KeyReadCuts

/-- Same-carrier native zero/write/sort/read composition. The sorted result
is constructed from the SAME raw producer call, and each selected getter
consumes THAT returned array. The only native premises are single-step cuts;
canonical Prepared provenance remains the named NBR_/NBS_ lower boundary. -/
theorem produce_sort_read (create : Carrier → Nat → Nat → KeyState)
    (zeroCut : NCE_Native_KeysZero create) (write : KeyState → KeyState)
    (writeCut : NCE_Native_KeysWrite write) (sort : NCE_SortCarrierCuts.Step)
    (sortCut : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier sort)
    (read : Read) (readCut : NCE_Native_KeysRead read) (caller : Carrier)
    (batch kind : Nat) (bb : batch < 2) (kb : kind < 3)
    (queries : ∀ j, j < 22 → caller.prepared.queries.val[j]!.val < 262144)
    (n : Usize) (count : n.val = (OraclePortSelectedDraft.batchPositions batch).length) :
    ∃ sorted,
      NCE_SortCarrierCuts.sort sort n.val (produce create write caller batch kind).caller
        (array (produce create write caller batch kind)) 1#usize n = ok (sorted,caller) ∧
      sorted.val.drop n.val = List.replicate (16-n.val) 0#u64 ∧
      ∀ cursor : Usize, cursor.val < n.val →
        read caller sorted cursor = ok
          (MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries caller.prepared.queries) batch kind
            ((OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries caller.prepared.queries) batch kind)[cursor.val]!),
            Usize.wrapping_add cursor 1#usize,sorted,caller) := by
  have raw := producer create zeroCut write writeCut caller batch kind bb kb queries
  obtain ⟨sorted,returned,front,suffix⟩ := NBJ_Keys.producer_sorted caller.prepared.queries batch kind n count
  have small : n.val ≤ 16 := by
    rw [count]
    unfold OraclePortSelectedDraft.batchPositions
    split <;> simp
  refine ⟨sorted,?_,suffix,?_⟩
  · rw [raw.2,NCE_SortCarrierCuts.sort_eq sort sortCut n.val caller _ 1#usize n small (Nat.sub_le _ _),
      raw.1,←NBI_Keys.producer_eq caller.prepared.queries batch kind,returned]
    rfl
  · intro cursor active
    rw [readCut caller sorted cursor (by omega)]
    rw [prefix_read sorted n.val _ _ front small cursor active]

#print axioms produce_sort_read
end AspisR1.NCE_KeysCarrierJoin
