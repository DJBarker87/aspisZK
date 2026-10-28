import NCM_LeafLoop
import NCE_KeysCarrierJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_KeyStream
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyCuts NCE_KeyProducerCuts

/-- Construct the actual sorted witness, then derive every unread key law
from THAT array and its native getter. No independently selected stream or
successful sort output is a hypothesis. -/
theorem produced (create : Carrier → Nat → Nat → KeyState)
    (zero : NCE_Native_KeysZero create) (write : KeyState → KeyState)
    (writeCut : NCE_Native_KeysWrite write) (sort : NCE_SortCarrierCuts.Step)
    (sortCut : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier sort)
    (get : NCE_KeyReadCuts.Read) (getCut : NCE_KeyReadCuts.NCE_Native_KeysRead get)
    (caller : Carrier) (batch kind : Nat) (bb : batch < 2) (kb : kind < 3)
    (queries : ∀ j, j < 22 → caller.prepared.queries.val[j]!.val < 262144)
    (n : Usize) (count : n.val = (OraclePortSelectedDraft.batchPositions batch).length) :
    ∃ sorted,
      NCE_SortCarrierCuts.sort sort n.val (produce create write caller batch kind).caller
        (array (produce create write caller batch kind)) 1#usize n = ok (sorted,caller) ∧
      NCM_LeafLoop.Stream sorted 0#usize (Port4B_KeyInstall.queries caller.prepared.queries) batch kind
        (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries caller.prepared.queries) batch kind) := by
  obtain ⟨sorted,returned,suffix,reads⟩ := NCE_KeysCarrierJoin.produce_sort_read create zero write writeCut sort sortCut get getCut caller batch kind bb kb queries n count
  refine ⟨sorted,returned,?_⟩
  intro j jb
  have length : (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries caller.prepared.queries) batch kind).length =
      (OraclePortSelectedDraft.batchPositions batch).length := by
    simp only [OraclePortFrozenOrder.sortedPositions,List.length_mergeSort]
  have active : j < n.val := by rw [count];omega
  have small : n.val ≤ 16 := by rw [count];unfold OraclePortSelectedDraft.batchPositions;split <;> decide
  let cursor : Usize := UScalar.ofNat j (by scalar_tac)
  have cursorVal : cursor.val = j := rfl
  have bound : cursor.val < 16 := by rw [cursorVal];omega
  have native := getCut caller sorted cursor bound
  have modeled := reads cursor (by rw [cursorVal];exact active)
  have value := congrArg (fun x => x.1) (Result.ok.inj (native.symm.trans modeled))
  simpa only [show (0#usize).val = 0 from rfl,Nat.zero_add,cursorVal] using value

#print axioms produced
end AspisR1.NCM_KeyStream
end
