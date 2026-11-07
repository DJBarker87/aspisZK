import PCI_DepositConvert
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositExtents
open PCI_DepositRange PCI_DepositConvert

def readShared {T : Type} (bytes : Slice T) (start last n : Usize) := do
 let xs ← core.slice.index.SliceIndexRangeUsizeSlice.index {start,«end»:=last} bytes
 core.array.TryFromSharedArraySlice.try_from n xs

theorem read {T : Type} (bytes : Slice T) (start last n : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length)
    (width : last.val-start.val=n.val) :
    readShared bytes start last n=ok (.Ok (arrayWindow bytes start last n ordered bounded width)) := by
 unfold readShared
 rw [index bytes start last ordered bounded]
 simp only [bind_tc_ok,shared bytes start last n ordered bounded width]

theorem owner (bytes : Slice U8) (extent : 80≤bytes.length) :
    readShared bytes 8#usize 40#usize 32#usize=
      ok (.Ok (arrayWindow bytes 8#usize 40#usize 32#usize (by scalar_tac) (by scalar_tac) (by scalar_tac))) :=
 read bytes _ _ _ (by scalar_tac) (by scalar_tac) (by scalar_tac)

theorem salt (bytes : Slice U8) (extent : 80≤bytes.length) :
    readShared bytes 48#usize 80#usize 32#usize=
      ok (.Ok (arrayWindow bytes 48#usize 80#usize 32#usize (by scalar_tac) (by scalar_tac) (by scalar_tac))) :=
 read bytes _ _ _ (by scalar_tac) (by scalar_tac) (by scalar_tac)

#print axioms read
#print axioms owner
#print axioms salt
end PCI_DepositExtents
