import R1Z.PV_RDCD_ZeroWorld
set_option autoImplicit false
namespace R1Z.PV_RDCD_ZeroTrace
open PV_RDCD_ZeroWorld

def trace : Nat → Nat → List Event
  | _,0 => []
  | address,n+1 => [.volatileWrite address 0,.asmReadBarrier address] ++ trace (address+1) n

theorem history {F : Type} (address n : Nat) (w : World F) :
    (native address n w).history=w.history++trace address n := by
  induction n generalizing address w with
  | zero => simp only [native,trace,List.append_nil]
  | succ n ih =>
    simp only [native,trace,ih,byte,List.append_assoc]

theorem trace_length (address n : Nat) : (trace address n).length=2*n := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih =>
    simp only [trace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

/-- The history witnesses writes even when the input byte is already zero.
A zero output value does not stand in for the write event. -/
theorem writes_recorded {F : Type} (address n : Nat) (w : World F) :
    (native address n w).history.length=w.history.length+2*n := by
  rw [history,List.length_append,trace_length]

theorem nonvacuous {F : Type} (frame : F) : ∃ w : World F, w.frame=frame :=
  ⟨⟨fun _ => 0,0,0,[],0,0,0,0,frame⟩,rfl⟩

#print axioms history
#print axioms trace_length
#print axioms writes_recorded
#print axioms nonvacuous
end R1Z.PV_RDCD_ZeroTrace
