import NBO_AccumulateAssociation
set_option autoImplicit false
noncomputable section
namespace NEI_AccumIndependentCounters
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open NBO_AccumulateAssociation
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g) = (x >>= fun a=>f a >>= g) := by
 cases x <;> rfl
/-- Model shell only: independent global and local counters, including TX2.
This does not discharge the frozen CodeField::from_m31 slice boundary. -/
theorem independent_counters (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : Stage2E) (b : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (raw : b.raw.val.length=64)
 (active : a.next.val<22) (localActive : b.terms.val<22) :
 verifier.accumulate_batched_with_node (sourceOps ops) p a node value b =
 AspisR1Stage2.verifier.accumulateWithOps (reference ops) p a node value b := by
 have next := Port3_Wrapping.checked_add a.next 1#usize (by change a.next.val+1≤4096;omega)
 have nativeShell : verifier.accumulate_batched_with_node (sourceOps ops) p a node value b =
   (do let mid ← prefixRun ops a node b
       let term ← lift (Usize.wrapping_add mid.terms 1#usize)
       let product ← (sourceOps ops).op3 value a.power
       let rhs ← (sourceOps ops).op2 a.rhs product
       (sourceOps ops).op15 11#u16 a.next rhs
       let power ← (sourceOps ops).op9 a.power p.rho
       let successor ← lift (Usize.wrapping_add a.next 1#usize)
       ok ({a with rhs:=rhs,power:=power,next:=successor},{mid with terms:=term})) := by
   unfold verifier.accumulate_batched_with_node prefixRun
   simp only [associate,bind_tc_ok]
 have referenceShell : AspisR1Stage2.verifier.accumulateWithOps (reference ops) p a node value b =
   (do let mid ← prefixRun ops a node b
       let term ← mid.terms+1#usize
       let product ← (sourceOps ops).op3 value a.power
       let rhs ← (sourceOps ops).op2 a.rhs product
       (sourceOps ops).op15 11#u16 a.next rhs
       let power ← (sourceOps ops).op9 a.power p.rho
       let successor ← a.next+1#usize
       ok ({a with rhs:=rhs,power:=power,next:=successor},{mid with terms:=term})) := by
   unfold AspisR1Stage2.verifier.accumulateWithOps reference prefixRun
   simp only [associate,bind_tc_ok]
 rw [nativeShell,referenceShell]
 cases hprefix : prefixRun ops a node b with
 | fail e => rfl
 | div => rfl
 | ok mid =>
   have terms := prefix_terms ops a node b mid size raw hprefix
   have term := Port3_Wrapping.checked_add mid.terms 1#usize
     (by rw [terms];change b.terms.val+1≤4096;omega)
   simp only [lift,bind_tc_ok,term,next]
#print axioms independent_counters
end NEI_AccumIndependentCounters
end
