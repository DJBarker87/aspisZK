import CheckpointBytes3Reader
set_option autoImplicit false
namespace AspisR1.NCI_WindowFrame

def window {α : Type} (xs : List α) (base width : Nat) := (xs.drop base).take width

theorem cell {α : Type} (xs : List α) (base width j : Nat)
    (hj : j < width) (bound : base+width ≤ xs.length) :
    (window xs base width)[j]'(by simp [window]; omega) =
      xs[base+j]'(by omega) := by
  simp [window, List.getElem_take, List.getElem_drop]

theorem after {α : Type} (xs : List α) (base start width n : Nat)
    (hbase : base ≤ start) (hwidth : start-base+n ≤ width) :
    window (window xs base width) (start-base) n = window xs start n := by
  simp only [window, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  · omega
  · omega
#print axioms cell
#print axioms after
end AspisR1.NCI_WindowFrame
