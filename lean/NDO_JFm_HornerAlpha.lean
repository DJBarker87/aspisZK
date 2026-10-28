import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFm_HornerAlpha
open Aeneas Aeneas.Std Result
open JFr_WordArithmetic JFr_HornerTrace

theorem transport {p : Array Q 28#usize} {a b : Array Q 10#usize}
    {r i j : Usize} {x y : Q} (t : Segment p a r i x j y)
    (same : Array.index_usize a r=Array.index_usize b r) : Segment p b r i x j y := by
  induction t with
  | refl => exact .refl _ _
  | step active dec challenge mul read add tail ih =>
    exact .step active dec (same.symm.trans challenge) mul read add ih

#print axioms transport
end AspisR1.JFm_HornerAlpha
