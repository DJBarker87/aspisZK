import CuSavingsTryGraph

/-! Adapter for the source frontend's retained associated-type layout.
Try keeps three associated types as fields; Residual has already lifted its
TryType to a parameter. This matches that split without erasing either parent.
Concrete infallible instances consume the checked extracted-method graph.
Generic frontend/source admission and final caller composition remain open. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsTryGraphRuntime
open Aeneas Aeneas.Std Result
open CuSavingsTryGraph

structure DynamicTry (Self : Type) where
  Output : Type
  Residual : Type
  Self_Clause1_TryType : Type
  value : Try Self Output Residual Self_Clause1_TryType

def DynamicTry.FromResidualInst {Self : Type} (inst : DynamicTry Self) :
    core.ops.try_trait.FromResidual Self inst.Residual := inst.value.FromResidualInst

def DynamicTry.ResidualInst {Self : Type} (inst : DynamicTry Self) :
    CuSavingsTryGraph.Residual inst.Residual inst.Output inst.Self_Clause1_TryType :=
  inst.value.ResidualInst

def DynamicTry.from_output {Self : Type} (inst : DynamicTry Self) :
    inst.Output → Result Self := inst.value.from_output

def DynamicTry.branch {Self : Type} (inst : DynamicTry Self) :
    Self → Result (core.ops.control_flow.ControlFlow inst.Residual inst.Output) :=
  inst.value.branch

abbrev Residual (R O TryType : Type) := CuSavingsTryGraph.Residual R O TryType

def Residual.TryInst {R O TryType : Type} (inst : Residual R O TryType) : DynamicTry TryType :=
  {Output:=O,Residual:=R,Self_Clause1_TryType:=TryType,
   value:=CuSavingsTryGraph.Residual.TryInst inst}

def neverTry (T : Type) : DynamicTry T :=
  {Output:=T,Residual:=Never,Self_Clause1_TryType:=T,value:=CuSavingsTryGraph.neverTry T}

def neverResidual (T : Type) : Residual Never T T := fun _ => neverCore T

theorem source_parent_output {R O TryType : Type} (inst : Residual R O TryType) :
    inst.TryInst.Output = O := by rfl

theorem source_parent_residual {R O TryType : Type} (inst : Residual R O TryType) :
    inst.TryInst.Residual = R := by rfl

theorem never_parent (T : Type) : (neverResidual T).TryInst = neverTry T := by rfl

theorem never_branch {T : Type} (value : T) :
    (neverTry T).branch value = .ok (.Continue value) := by rfl

theorem never_wrap {T : Type} (value : T) :
    (neverResidual T).TryInst.from_output value = .ok value := by rfl

#print axioms DynamicTry
#print axioms DynamicTry.FromResidualInst
#print axioms DynamicTry.ResidualInst
#print axioms DynamicTry.from_output
#print axioms DynamicTry.branch
#print axioms Residual.TryInst
#print axioms neverTry
#print axioms neverResidual
#print axioms source_parent_output
#print axioms source_parent_residual
#print axioms never_parent
#print axioms never_branch
#print axioms never_wrap
end AspisR1.CuSavingsTryGraphRuntime
