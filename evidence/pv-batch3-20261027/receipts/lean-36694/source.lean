import PV_B3_BoundedLoop
import PV_B3_ArrayCarrier
namespace PV_B3_FiniteLoopTransport
open Aeneas Aeneas.Std Result ControlFlow PV_B3_ArrayCarrier
set_option autoImplicit false

def controlMap {A B C D : Type} (f : A → C) (g : B → D) :
    ControlFlow A B → ControlFlow C D
  | .cont x => .cont (f x)
  | .done y => .done (g y)

-- The body square is an explicit obligation. This theorem transports all
-- Result tags; it neither assumes successful arithmetic nor unfolds a run.
theorem bounded {A B C D : Type}
    (newBody : A → Result (ControlFlow A B)) (oldBody : C → Result (ControlFlow C D))
    (f : A → C) (g : B → D)
    (comm : ∀ x, oldBody (f x) = resultMap (controlMap f g) (newBody x))
    (rank : A → Nat)
    (decreases : ∀ x y, newBody x = ok (cont y) → rank y < rank x) :
    ∀ n x, rank x ≤ n → loop oldBody (f x) =
      resultMap g (PV_B3_BoundedLoop.bounded newBody n x) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [loop.eq_def, comm x]
    cases hb : newBody x with
    | fail e => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
    | div => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
    | ok cf =>
      cases cf with
      | done y => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
      | cont y => have hd := decreases x y hb; omega
  | succ n ih =>
    intro x hx
    rw [loop.eq_def, comm x]
    cases hb : newBody x with
    | fail e => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
    | div => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
    | ok cf =>
      cases cf with
      | done y => simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
      | cont y =>
        simp only [PV_B3_BoundedLoop.bounded, hb, resultMap, controlMap, bind_tc_ok]
        exact ih y (by have hd := decreases x y hb; omega)

theorem source {A B C D : Type}
    (newBody : A → Result (ControlFlow A B)) (oldBody : C → Result (ControlFlow C D))
    (f : A → C) (g : B → D)
    (comm : ∀ x, oldBody (f x) = resultMap (controlMap f g) (newBody x))
    (rank : A → Nat)
    (decreases : ∀ x y, newBody x = ok (cont y) → rank y < rank x) (x : A) :
    loop oldBody (f x) = resultMap g (loop newBody x) := by
  exact (bounded newBody oldBody f g comm rank decreases (rank x) x (Nat.le_refl _)).trans
    (congrArg (resultMap g)
      (PV_B3_BoundedLoop.source_eq_bounded newBody rank decreases (rank x) x (Nat.le_refl _)).symm)

#print axioms controlMap
#print axioms bounded
#print axioms source
end PV_B3_FiniteLoopTransport
