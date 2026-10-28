import R1Z.ProverRwP7TraceCloneSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7TraceCloneTotal
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem vector {T : Type} (inst : core.clone.Clone T)
    (element : ∀ x, inst.clone x = ok x) (v : alloc.vec.Vec T) :
    (core.clone.CloneallocvecVec inst).clone v = ok v := by
  obtain ⟨out,ho,he⟩ := WP.spec_imp_exists (Slice.clone_spec (s := v) (fun x _ => element x))
  rw [← he] at ho
  exact ho

theorem array {T : Type} {N : Usize} (inst : core.clone.Clone T)
    (element : ∀ x, inst.clone x = ok x) (v : Array T N) :
    core.array.CloneArray.clone inst v = ok v := by
  obtain ⟨out,ho,he⟩ := WP.spec_imp_exists
    (core.array.CloneArray.clone_spec inst v (fun x _ => element x))
  rw [← he] at ho
  exact ho

-- Source result under retained array/Vec clone semantics, not an allocator or
-- native Drop adequacy theorem. No clone-success/output premise is supplied.
theorem source (ops : ExternalFuns)
    (x : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    @ProverRwP7TraceCloneSource.trace_clone _ (ProverRwP6BodyStore.selected ops) x = ok x := by
  letI : ExternalFuns := ProverRwP6BodyStore.selected ops
  let m : core.clone.Clone U32 := ProverRwP7TraceCloneSource.aspis_core.field.M31.Insts.CoreCloneClone
  have hm : ∀ a, m.clone a = ok a := by intro a; rfl
  have hv := array (core.clone.CloneallocvecVec m) (vector m hm) x.c1
  unfold ProverRwP7TraceCloneSource.trace_clone
    ProverRwP7TraceCloneSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
  rw [hv]
  cases x
  rfl
#print axioms vector
#print axioms array
#print axioms source
end R1Z.ProverRwP7TraceCloneTotal
