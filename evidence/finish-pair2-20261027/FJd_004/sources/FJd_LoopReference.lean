import FJd_PointReference
import FJc_InstalledFinalPart0
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_LoopReference
variable {K : Type} [Field K]
/-- Fold used by the safe reference on the original ten coordinates. -/
def successorStep (z : Fin 10 → K) (state : K × (Fin 10 → K)) (i : Fin 10) :
    K × (Fin 10 → K) :=
  let bc := z i * state.1
  (bc,Function.update state.2 i (z i+state.1-(bc+bc)))
def successor (z : Fin 10 → K) : Fin 10 → K :=
  ((List.finRange 10).reverse.foldl (successorStep z) (1,z)).2

def double (x : K) : K := x*x+(x*x)-1

def circleStep (state : K × (Fin 5 → Fin 4 → K)) (d : Fin 5) :=
  let x := state.1
  let y := double x
  (double y,Function.update state.2 d
    (fun s => match s.val with | 0 => 1 | 1 => x | 2 => y | _ => x*y))

def tensor64 (f : Fin 5 → Fin 4 → K) (j : Fin 64) : K :=
  ((1*f 2 ⟨j.val%4,Nat.mod_lt _ (by omega)⟩)*
    f 3 ⟨j.val/4%4,Nat.mod_lt _ (by omega)⟩)*
    f 4 ⟨j.val/16,by have := j.isLt; omega⟩

variable {E : Type} [Field E]
def dot64 (a b : Fin 64 → E) : E :=
  (List.finRange 64).foldl (fun acc j=>acc+a j*b j) 0

theorem double_polynomial (x : K) : double x=2*x^2-1 := by
  unfold double
  ring

theorem successor_step_value (z : Fin 10 → K) (c : K) (out : Fin 10 → K) (i : Fin 10) :
    (successorStep z (c,out) i).2 i=z i+c-2*(z i*c) := by
  change Function.update out i (z i+c-(z i*c+z i*c)) i=_
  rw [Function.update_self]
  ring

theorem successor_step_carry (z : Fin 10 → K) (c : K) (out : Fin 10 → K) (i : Fin 10) :
    (successorStep z (c,out) i).1=z i*c := rfl

theorem successor_step_frame (z : Fin 10 → K) (c : K) (out : Fin 10 → K)
    (i j : Fin 10) (h : j≠i) :
    (successorStep z (c,out) i).2 j=out j := by
  simp only [successorStep,Function.update_of_ne h]
#print axioms double_polynomial
#print axioms successor_step_value
#print axioms successor_step_carry
#print axioms successor_step_frame
end AspisR1.FJd_LoopReference
end
