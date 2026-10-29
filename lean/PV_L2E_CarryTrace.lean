import PV_L2D_DivisionBounds
set_option autoImplicit false
namespace PV_L2E_CarryTrace
open PV_L2D_DivisionBounds

inductive Event where
  | guard (index : Nat) (taken : Bool)
  | read (index : Nat)
  | write (index : Nat)
  deriving DecidableEq

def plan : Nat → Nat → List Event
  | i,0 => [.guard i false]
  | i,n+1 => [.guard i true,.read i,.write i] ++ plan (i+1) n

def run : Nat → Nat → List Nat → (List Nat × Nat) × List Event
  | i,a,[] => (([],a),[.guard i false])
  | i,a,d::ds =>
    let tail := run (i+1) ((d+a)/P) ds
    (((d+a)%P::tail.1.1,tail.1.2),
      [.guard i true,.read i,.write i] ++ tail.2)

theorem length (i a : Nat) (ds : List Nat) :
    (run i a ds).1.1.length=ds.length := by
  induction ds generalizing i a with
  | nil => rfl
  | cons d ds ih => simp only [run,List.length_cons,ih]

theorem trace_constant (i a : Nat) (ds : List Nat) :
    (run i a ds).2=plan i ds.length := by
  induction ds generalizing i a with
  | nil => rfl
  | cons d ds ih => simp only [run,List.length_cons,plan,ih]

theorem digit_bounds (i a : Nat) (ds : List Nat) :
    ∀ d∈(run i a ds).1.1,d<P := by
  induction ds generalizing i a with
  | nil => simp [run]
  | cons d ds ih =>
    intro x hx
    simp only [run,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ _ hx

theorem one_step_carry (d a : Nat) (hd : d<P) (ha : a≤P) :
    (d+a)/P≤1 := by
  have h : d+a<2*P := by omega
  have hq : (d+a)/P<2 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  omega

theorem final_carry (i a : Nat) (ds : List Nat) (ha : a≤P)
    (hd : ∀ d∈ds,d<P) (nonempty : ds≠[]) :
    (run i a ds).1.2≤1 := by
  induction ds generalizing i a with
  | nil => exact False.elim (nonempty rfl)
  | cons d ds ih =>
    have hc := one_step_carry d a (hd d (by simp)) ha
    cases ds with
    | nil => exact hc
    | cons e es =>
      exact ih (i+1) ((d+a)/P) (Nat.le_trans hc (by decide))
        (fun x hx => hd x (by simp [hx])) (by simp)

#print axioms length
#print axioms trace_constant
#print axioms digit_bounds
#print axioms one_step_carry
#print axioms final_carry
end PV_L2E_CarryTrace
