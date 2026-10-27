import FJd_LoopReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_CircleReference
variable {K : Type} [Field K]
/-- Explicit repeated-circle polynomial; no concrete endpoint is evaluated. -/
def repeat : Nat → K → K
  | 0,x => x
  | n+1,x => FJd_LoopReference.double (repeat n x)

def factors (x y : K) (d : Fin 5) (s : Fin 4) : K :=
  if d.val=0 then
    match s.val with | 0=>1 | 1=>y | 2=>x | _=>x*y
  else
    let a:=repeat (2*d.val-1) x
    let b:=repeat (2*d.val) x
    match s.val with | 0=>1 | 1=>a | 2=>b | _=>a*b

theorem successor (n : Nat) (x : K) :
    repeat (n+1) x=2*(repeat n x)^2-1 :=
  FJd_LoopReference.double_polynomial _

theorem twice (n : Nat) (x : K) :
    FJd_LoopReference.double (FJd_LoopReference.double (repeat n x))=repeat (n+2) x := rfl

theorem next_x (d : Nat) (x : K) (h : 0<d) :
    FJd_LoopReference.double (FJd_LoopReference.double (repeat (2*d-1) x))=
      repeat (2*(d+1)-1) x := by
  rw [twice]
  congr 1
  omega

theorem next_y (d : Nat) (x : K) (h : 0<d) :
    FJd_LoopReference.double (repeat (2*d-1) x)=repeat (2*d) x := by
  have hi : 2*d=(2*d-1)+1 := by omega
  rw [hi]
  rfl
#print axioms successor
#print axioms twice
#print axioms next_x
#print axioms next_y
end AspisR1.FJd_CircleReference
end
