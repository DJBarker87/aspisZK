import R1Z.PDict_RemainingDictionary231
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingValues231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingDictionary231 (native selected)

/-- Source result under the retained array/Vec model. Native allocation and
Drop/world adequacy remain separate; no clone-success premise is supplied. -/
theorem clone_source [ExternalTypes] (x : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    PDict_RemainingLeafSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone x = ok x := by
  let m : core.clone.Clone U32 := PDict_RemainingLeafSource.aspis_core.field.M31.Insts.CoreCloneClone
  have hm : ∀ a, m.clone a = ok a := by intro a; rfl
  have hv := ProverRwP7TraceCloneTotal.array (core.clone.CloneallocvecVec m)
    (ProverRwP7TraceCloneTotal.vector m hm) x.c1
  unfold PDict_RemainingLeafSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
  rw [hv]
  cases x
  rfl

theorem op231_value (base : ExternalTypes)
    (ops : @ExternalFuns (native base))
    (x : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    (selected base ops).op231 x = ok x := by
  letI : ExternalTypes := native base
  exact clone_source x

theorem op247_value (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (tag : U16) (index : Usize)
    (x : aspis_core.field.wide_exact.WideExact) :
    (selected base ops).op247 tag index x = ok () := rfl

#print axioms clone_source
#print axioms op231_value
#print axioms op247_value
end R1Z.PDict_RemainingValues231
