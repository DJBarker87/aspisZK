import NCM_OpeningView
import NCE_KeyOpeningJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_KeyView
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyReadCuts

def read (get : Read) (reader : Reader) (caller : Carrier)
    (keys : Array U64 16#usize) (cursor : Usize) (batch : Nat) :
    Result (U64 × Usize × Slice U8 × Array U64 16#usize × Carrier) := do
  let got ← get caller keys cursor
  let opened ← NCM_OpeningView.read reader got.2.2.2 (Port4B_NativeLeaf.openingIndex (NCE_KeyOpeningJoin.lo batch) got.1)
  ok (got.1,got.2.1,opened.1,got.2.2.1,opened.2)

/-- The ACTUAL returned packed key chooses the next borrowed view and its
source slice, with the SAME caller and sorted backing array. -/
theorem observation (get : Read) (getCut : NCE_Native_KeysRead get)
    (reader : Reader) (readerCut : NCE_Native_Opening reader) (caller : Carrier)
    (keys : Array U64 16#usize) (cursor : Usize) (bound : cursor.val < 16)
    (q : Fin 22 → Fin 262144) (batch kind selected : Nat)
    (member : selected ∈ OraclePortSelectedDraft.batchPositions batch)
    (key : keys.val[cursor.val]! = MultiproofConeSortOrder.packed q batch kind selected)
    (size : caller.proof.val.length = 57607) :
    ∃ view,
      Port4B_Opening.opening caller.proof
        (Port4B_NativeLeaf.openingIndex (NCE_KeyOpeningJoin.lo batch)
          (MultiproofConeSortOrder.packed q batch kind selected)) = ok view ∧
      view.val.length = 832 ∧
      read get reader caller keys cursor batch =
        ok (MultiproofConeSortOrder.packed q batch kind selected,Usize.wrapping_add cursor 1#usize,view,keys,caller) := by
  have base : (NCE_KeyOpeningJoin.lo batch).val = (if batch=0 then 0 else 10) := by
    unfold NCE_KeyOpeningJoin.lo
    split <;> rfl
  have decoded := Port4B_KeyDecode.packed q batch kind selected member (NCE_KeyOpeningJoin.lo batch) base
  have position := MultiproofConeKeyAdapters.position_bounds batch selected member
  obtain ⟨view,source,len,opened⟩ := NCM_OpeningView.observation reader readerCut caller
    (Port4B_NativeLeaf.openingIndex (NCE_KeyOpeningJoin.lo batch) (MultiproofConeSortOrder.packed q batch kind selected))
    size (by rw [decoded.2];exact position.2)
  refine ⟨view,source,len,?_⟩
  simp only [read,getCut caller keys cursor bound,bind_tc_ok,key,opened]

#print axioms observation
end AspisR1.NCM_KeyView
end
