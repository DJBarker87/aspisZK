import RPu_FJc_DigitIndices
import RPt_FJc_ReadSlot
import RPu_FIp_ArrayValue
import RPu_FGm_WideScaleValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowModel
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE)

def perm (i : Nat) : Nat :=
  match FIo_Native.weights.PERM.val[i]? with | some x=>x.val | none=>0

def value (ap0 ap1 : Array NE 4#usize) (s : Nat) : AspisWideTower.WideExact :=
  (decodeM FIo_Native.weights.QUARTER*decodeM FIo_Native.weights.QUARTER) •
    (FIp_ArrayValue.value ap0 (perm (s%4))*FIp_ArrayValue.value ap1 (perm (s/4)))

theorem perm_read (i p : Usize) (run : Array.index_usize FIo_Native.weights.PERM i=ok p) :
    perm i.val=p.val := by
  simp only [perm,FJc_ReadSlot.slot _ i p run]
#print axioms perm_read
end AspisR1.FJc_LowModel
end
