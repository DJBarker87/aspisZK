import PCI_DepositRange
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositConvert
open PCI_DepositRange

def arrayWindow {T : Type} (bytes : Slice T) (start last n : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length)
    (width : last.val-start.val=n.val) : Array T n :=
  ⟨(window bytes start last ordered bounded).val,by
    change (window bytes start last ordered bounded).length=n.val
    exact (length bytes start last ordered bounded).trans width⟩

theorem shared {T : Type} (bytes : Slice T) (start last n : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length)
    (width : last.val-start.val=n.val) :
    core.array.TryFromSharedArraySlice.try_from n (window bytes start last ordered bounded)=
      ok (.Ok (arrayWindow bytes start last n ordered bounded width)) := by
  have h : (window bytes start last ordered bounded).len=n := by
    apply UScalar.eq_of_val_eq
    exact (length bytes start last ordered bounded).trans width
  simp only [core.array.TryFromSharedArraySlice.try_from,h,↓reduceDIte]
  rfl

theorem copy {T : Type} (bytes : Slice T) (start last n : Usize) (inst : core.marker.Copy T)
    (ordered : start≤last) (bounded : last.val≤bytes.length)
    (width : last.val-start.val=n.val) :
    core.array.TryFromArrayCopySlice.try_from n inst (window bytes start last ordered bounded)=
      ok (.Ok (arrayWindow bytes start last n ordered bounded width)) := by
  have h : (window bytes start last ordered bounded).length=n.val :=
    (length bytes start last ordered bounded).trans width
  simp only [core.array.TryFromArrayCopySlice.try_from,h,↓reduceDIte]
  rfl

#print axioms shared
#print axioms copy
end PCI_DepositConvert
