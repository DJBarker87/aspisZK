import NCE_KeyReadCuts
import NCE_OpeningCuts
import Port4B_KeyDecode

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_KeyOpeningJoin
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyReadCuts
attribute [local irreducible] NBJ_WindowCover.image MultiproofConeSortOrder.packed

def lo (batch : Nat) : Usize := if batch = 0 then 0#usize else 10#usize

/-- Logical read-image continuation of the ACTUAL returned raw key. This
constructs a value observation of the borrowed opening; it does not assert
that the Rust source allocates/copies an832-byte buffer or add native work. -/
def keyOpening (get : Read) (reader : Reader) (caller : Carrier)
    (keys : Array U64 16#usize) (cursor : Usize) (batch : Nat) :
    Result (U64 × Usize × List U8 × Array U64 16#usize × Carrier) := do
  let got ← get caller keys cursor
  let opened ← readWindow reader (Port4B_NativeLeaf.openingIndex (lo batch) got.1).val 832 0 got.2.2.2
  ok (got.1,got.2.1,opened.1,got.2.2.1,opened.2)

/-- One selected-key fact (available from produce_sort_read) composes with
native getter and opening-byte cuts on the SAME caller. The imported packed
rebasing theorem proves the next opening index and its native domain. No
independently successful opening/digest/leaf call is a hypothesis. -/
theorem selected_opening (get : Read) (getCut : NCE_Native_KeysRead get)
    (reader : Reader) (readerCut : NCE_Native_Opening reader) (caller : Carrier)
    (keys : Array U64 16#usize) (cursor : Usize) (bound : cursor.val < 16)
    (q : Fin 22 → Fin 262144) (batch kind selected : Nat)
    (member : selected ∈ OraclePortSelectedDraft.batchPositions batch)
    (key : keys.val[cursor.val]! = MultiproofConeSortOrder.packed q batch kind selected)
    (size : caller.proof.val.length = 57607) :
    keyOpening get reader caller keys cursor batch =
      ok (MultiproofConeSortOrder.packed q batch kind selected,Usize.wrapping_add cursor 1#usize,
        NBJ_WindowCover.image (fun k => caller.proof.val[k]!) (10055+832*selected) 832,keys,caller) := by
  have base : (lo batch).val = (if batch = 0 then 0 else 10) := by
    unfold lo
    split <;> rfl
  have decoded := Port4B_KeyDecode.packed q batch kind selected member (lo batch) base
  have position := MultiproofConeKeyAdapters.position_bounds batch selected member
  rw [keyOpening,getCut caller keys cursor bound]
  simp only [bind_tc_ok]
  rw [key,decoded.2,opening reader readerCut caller selected size position.2]
  simp only [bind_tc_ok] <;> rfl

#print axioms selected_opening
end AspisR1.NCE_KeyOpeningJoin
end
