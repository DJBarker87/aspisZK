import PCI_DepositExtents
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositCopyExtents
open PCI_DepositRange PCI_DepositConvert

def readCopy (bytes : Slice U8) (start last n : Usize) := do
 let xs ← core.slice.index.SliceIndexRangeUsizeSlice.index {start,«end»:=last} bytes
 core.array.TryFromArrayCopySlice.try_from n core.marker.CopyU8 xs

theorem read (bytes : Slice U8) (start last n : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length)
    (width : last.val-start.val=n.val) :
    readCopy bytes start last n=ok (.Ok (arrayWindow bytes start last n ordered bounded width)) := by
 unfold readCopy
 rw [index bytes start last ordered bounded]
 simp only [bind_tc_ok,copy bytes start last n core.marker.CopyU8 ordered bounded width]

theorem declared (bytes : Slice U8) (extent : 80≤bytes.length) :
    readCopy bytes 6#usize 8#usize 2#usize=
      ok (.Ok (arrayWindow bytes 6#usize 8#usize 2#usize (by scalar_tac) (by scalar_tac) (by scalar_tac))) :=
 read bytes _ _ _ (by scalar_tac) (by scalar_tac) (by scalar_tac)

theorem amount (bytes : Slice U8) (extent : 80≤bytes.length) :
    readCopy bytes 40#usize 44#usize 4#usize=
      ok (.Ok (arrayWindow bytes 40#usize 44#usize 4#usize (by scalar_tac) (by scalar_tac) (by scalar_tac))) :=
 read bytes _ _ _ (by scalar_tac) (by scalar_tac) (by scalar_tac)

#print axioms read
#print axioms declared
#print axioms amount
end PCI_DepositCopyExtents
