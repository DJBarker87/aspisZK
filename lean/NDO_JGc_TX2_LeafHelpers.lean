import NDO_JGc_TX2_M2Leaves
import RPt_JFn_ValueBlock
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_LeafHelpers
open Aeneas Aeneas.Std Result

theorem four {A : Type} (xs c0 c1 c2 c3 : List A) (length : xs.length=128)
    (h0 : (xs.drop 0).take 32=c0) (h1 : (xs.drop 32).take 32=c1)
    (h2 : (xs.drop 64).take 32=c2) (h3 : (xs.drop 96).take 32=c3) :
    xs=c0++c1++c2++c3 := by
  have split : xs.take 128=(xs.take 32)++(xs.drop 32).take 32++
      (xs.drop 64).take 32++(xs.drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,List.append_assoc]
  have h0' : xs.take 32=c0 := by simpa only [List.drop_zero] using h0
  rw [List.take_of_length_le (by omega),h0',h1,h2,h3] at split
  exact split
#print axioms four
end AspisR1.JGc_TX2_LeafHelpers
end
