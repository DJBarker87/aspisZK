import FGm_ArrayValue
import FGm_RangeDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_SubsetSelection
open Aeneas Aeneas.Std Result

/-- The actual source mask test, including failed reads/shifts. This is a
local operational selector; identifying its table with model inactive weights
is a separate obligation. -/
def selected (group bit : Usize) : Bool :=
  match Array.index_usize FIo_Native.weights.S2_INACTIVE_MASKS group,
    (1#u16 <<< bit) with
  | ok mask,ok shift => mask &&& shift != 0#u16
  | _,_ => false

theorem reached (group bit : Usize) (mask shift : U16)
    (hm : Array.index_usize FIo_Native.weights.S2_INACTIVE_MASKS group=ok mask)
    (hs : (1#u16 <<< bit)=ok shift) :
    selected group bit=(mask &&& shift != 0#u16) := by
  simp only [selected,hm,hs]

#print axioms reached
end AspisR1.FGm_SubsetSelection
end
