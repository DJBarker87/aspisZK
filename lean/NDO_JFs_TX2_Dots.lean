import NDO_JFs_TX2_Four
import NDO_JFr_TX2_DotsBinding
import RPt_FIp_DotsOutputCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Dots
open Aeneas Aeneas.Std Result

def nativeValue (i : Fin 12) : Array FIo_Install.NE 4#usize := Classical.choose (JFs_TX2_Four.source i)
def value (i : Fin 12) : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray (nativeValue i)

theorem native (i : Fin 12) :
    FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value (JFn_Values.position i))
      JFr_TX2_FirstLane.native=ok (nativeValue i) := (Classical.choose_spec (JFs_TX2_Four.source i)).1

theorem adapter (i : Fin 12) :
    FIp_DotsAdapter.dots (JFo_Opening.value (JFn_Values.position i)) JFr_TX2_Powers.value=ok (value i) := by
  change (do let out ← FIp_NativeDots.fast_dots.four_dots
               (JFo_Opening.value (JFn_Values.position i)) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok (value i)
  rw [native i,bind_tc_ok]
  rfl

theorem source (seed : Port3_NativeQueryBody.Ops) (i : Fin 12) :
    (JFr_TX2_DotsBinding.ops seed).op20 (JFo_Opening.value (JFn_Values.position i))
      JFr_TX2_Powers.value=ok (value i) := by
  rw [JFr_TX2_DotsBinding.dots]
  exact adapter i

theorem canonical (i : Fin 12) : ∀ x∈(value i).val,Port4C_QueryArithmetic.CanonE x :=
  FIp_DotsOutputCanonical.all _ _ _ (adapter i)

#print axioms native
#print axioms adapter
#print axioms source
#print axioms canonical
end AspisR1.JFs_TX2_Dots
end
