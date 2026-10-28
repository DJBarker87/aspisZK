import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PDict_RemainingLeafSource
open Aeneas Aeneas.Std Result ProverRwFull
def aspis_core.field.M31.Insts.CoreCloneClone.clone
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  ok self

def aspis_core.field.M31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.M31 := {
  clone := aspis_core.field.M31.Insts.CoreCloneClone.clone
}

def aspis_r1_cost_probe.trace.value
  (tag : Std.U16) (index : Std.Usize)
  (x : aspis_core.field.wide_exact.WideExact) :
  Result Unit
  := do
  ok ()

def
  aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
  (self : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  let a ←
    core.array.CloneArray.clone (core.clone.CloneallocvecVec
      aspis_core.field.M31.Insts.CoreCloneClone) self.c1
  ok { c1 := a }


#print axioms aspis_core.field.M31.Insts.CoreCloneClone.clone
#print axioms aspis_core.field.M31.Insts.CoreCloneClone
#print axioms aspis_r1_cost_probe.trace.value
#print axioms aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
end PDict_RemainingLeafSource
