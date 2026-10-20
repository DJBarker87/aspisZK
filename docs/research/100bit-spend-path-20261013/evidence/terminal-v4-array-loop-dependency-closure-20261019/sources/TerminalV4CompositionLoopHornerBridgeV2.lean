import TerminalV4CompositionLoopExactValueV6

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.TerminalV4CompositionLoopHornerBridge
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R17.QM31WordTower.Q
abbrev decode := AspisR1.TerminalV4QM31TowerCurrent.decode

def listCoefficient (items : List QM) (i : Nat) : ExactQM :=
  match items.reverse[i]? with
  | none => 0
  | some x => decode x

def natHorner (coefficients : Nat → ExactQM) (linear : ExactQM) :
    Nat → ExactQM → ExactQM
  | 0, acc => acc
  | n + 1, acc => natHorner coefficients linear n
      (linear * acc + coefficients n)

theorem natHorner_congr_below (c d : Nat → ExactQM) (linear acc : ExactQM)
    (n : Nat) (h : ∀ i < n, c i = d i) :
    natHorner c linear n acc = natHorner d linear n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      simp only [natHorner]
      rw [h n (Nat.lt_succ_self n)]
      exact ih (linear * acc + d n) (by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi))

theorem listCoefficient_cons_at_length (x : QM) (xs : List QM) :
    listCoefficient (x :: xs) xs.length = decode x := by
  unfold listCoefficient
  rw [List.reverse_cons]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem listCoefficient_cons_before_length (x : QM) (xs : List QM) :
    ∀ i < xs.length, listCoefficient (x :: xs) i = listCoefficient xs i := by
  intro i hi
  unfold listCoefficient
  rw [List.reverse_cons]
  rw [List.getElem?_append_left (by simpa using hi)]

theorem listHorner_eq_natHorner (items : List QM) (linear acc : ExactQM) :
    AspisR1.TerminalV4CompositionLoopExactValue.listHorner linear items acc =
      natHorner (listCoefficient items) linear items.length acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [AspisR1.TerminalV4CompositionLoopExactValue.listHorner,
        List.length_cons, natHorner]
      rw [listCoefficient_cons_at_length]
      rw [natHorner_congr_below (listCoefficient (x :: xs))
        (listCoefficient xs) linear (linear * acc + decode x) xs.length
        (listCoefficient_cons_before_length x xs)]
      exact ih (linear * acc + decode x)

#print axioms listHorner_eq_natHorner
end AspisR1.TerminalV4CompositionLoopHornerBridge
