import NDO_JGe_Payload29
import NDO_JGe_Payload30
set_option autoImplicit false
namespace AspisR1.JGo_TX2_Windows
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.proof

theorem cell (off i : Nat) (hi : i<7) :
    ((JFw_Frames.window off 224).val.drop (32*i)).take 32=
      (JFw_Frames.window (off+32*i) 32).val := by
  simp only [JFw_Frames.window,List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : 32≤224-32*i)]
#print axioms cell
end AspisR1.JGo_TX2_Windows
