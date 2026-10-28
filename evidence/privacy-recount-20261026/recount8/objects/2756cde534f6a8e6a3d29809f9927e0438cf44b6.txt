import R1Z.ProverRwQueryPublish
set_option autoImplicit false
namespace R1Z.ProverRwQueryTrace
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
variable [ExternalTypes] [ExternalFuns]

def finite (q : Queries) : Nat → Usize → Result Unit
  | 0,_ => ok ()
  | fuel+1,i => do
    let u ← Array.index_usize q i
    let we ← aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 u
    trace.value 5#u16 i we
    finite q fuel (Usize.wrapping_add i 1#usize)

theorem loop_bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a=(do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => ok out) := by
  rw [loop]
  cases step a <;> rfl

theorem loop_finite (q : Queries) (fuel : Nat) (i : Usize) (bound : i.val+fuel=22) :
    host_transcript.trace_queries_loop q i=finite q fuel i := by
  unfold host_transcript.trace_queries_loop
  induction fuel generalizing i with
  | zero =>
    have stop : ¬ i<22#usize := by change ¬i.val<22; omega
    rw [loop_bind]
    simp only [host_transcript.trace_queries_loop.body,stop,if_false,bind_tc_ok,finite]
  | succ fuel ih =>
    have go : i<22#usize := by change i.val<22; omega
    have add := ProverRwQueryTransition.wrapping_succ i (by omega)
    rw [loop_bind]
    simp only [host_transcript.trace_queries_loop.body,go,if_true,finite,lift,bind_tc_ok,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro v hv)
    try simp only [lift,bind_tc_ok]
    exact ih (Usize.wrapping_add i 1#usize) (by omega)

theorem trace_finite (q : Queries) : host_transcript.trace_queries q=finite q 22 0#usize :=
  loop_finite q 22 0#usize (by rfl)

#print axioms loop_bind
#print axioms loop_finite
#print axioms trace_finite
end R1Z.ProverRwQueryTrace
