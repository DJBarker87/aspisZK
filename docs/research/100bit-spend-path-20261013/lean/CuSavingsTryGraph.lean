import AspisR1CuArraySource.NeverOperations

/-! A productive representation of the Try/Residual parent dictionary graph.
The original Self and Residual's TryType are separate parameters. All parent
nodes retain both Output and Residual types. No cyclic inductive value, axiom,
or identification of the original Self with TryType is required.

The concrete infallible graph consumes exact extracted standard methods. Its
generic frontend dictionary/source admission is a separate open obligation. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsTryGraph
open Aeneas Aeneas.Std Result

abbrev Core := core.ops.try_trait.Try

/-- Each successive parent observation has the declared output/residual. -/
abbrev Residual (R O TryType : Type) := Nat → Core TryType O R

structure Try (Self O R TryType : Type) where
  FromResidualInst : core.ops.try_trait.FromResidual Self R
  ResidualInst : Residual R O TryType
  from_output : O → Result Self
  branch : Self → Result (core.ops.control_flow.ControlFlow R O)

def Try.core {Self O R TryType : Type} (inst : Try Self O R TryType) : Core Self O R :=
  {FromResidualInst:=inst.FromResidualInst,from_output:=inst.from_output,branch:=inst.branch}

/-- Traversing a Residual parent retains a productive tail of dictionaries. -/
def Residual.TryInst {R O TryType : Type} (inst : Residual R O TryType) :
    Try TryType O R TryType :=
  {FromResidualInst:=(inst 0).FromResidualInst,
   ResidualInst:=fun n => inst (n+1),
   from_output:=(inst 0).from_output,branch:=(inst 0).branch}

theorem parent_head {R O TryType : Type} (inst : Residual R O TryType) :
    inst.TryInst.core = inst 0 := by rfl

theorem parent_tail {R O TryType : Type} (inst : Residual R O TryType) (n : Nat) :
    inst.TryInst.ResidualInst n = inst (n+1) := by rfl

abbrev Never := AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuitResidual

def neverCore (T : Type) : Core T T Never :=
  {FromResidualInst:=
     AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitFromResidualNeverShortCircuitResidual T,
   from_output:=AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitTry.from_output,
   branch:=AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitTry.branch}

/-- Both Rust parent links are present. The tail is productive and concrete. -/
def neverTry (T : Type) : Try T T Never T :=
  {FromResidualInst:=(neverCore T).FromResidualInst,
   ResidualInst:=fun _ => neverCore T,
   from_output:=(neverCore T).from_output,branch:=(neverCore T).branch}

theorem never_core (T : Type) : (neverTry T).core = neverCore T := by rfl

theorem never_parent (T : Type) :
    (neverTry T).ResidualInst.TryInst = neverTry T := by rfl

theorem never_observation (T : Type) (n : Nat) :
    (neverTry T).ResidualInst n = neverCore T := by rfl

theorem never_from_output {T : Type} (value : T) :
    (neverTry T).from_output value = .ok value := by rfl

theorem never_branch {T : Type} (value : T) :
    (neverTry T).branch value = .ok (.Continue value) := by rfl

theorem never_parent_branch {T : Type} (n : Nat) (value : T) :
    ((neverTry T).ResidualInst n).branch value = .ok (.Continue value) := by rfl

theorem never_from_output_then_branch {T : Type} (value : T) :
    (do let self ← (neverTry T).from_output value
        (neverTry T).branch self) = .ok (.Continue value) := by rfl

theorem never_residual_unreachable (value : Never) : False := by cases value

#print axioms Try
#print axioms Residual.TryInst
#print axioms parent_head
#print axioms parent_tail
#print axioms neverTry
#print axioms never_core
#print axioms never_parent
#print axioms never_observation
#print axioms never_from_output
#print axioms never_branch
#print axioms never_parent_branch
#print axioms never_from_output_then_branch
#print axioms never_residual_unreachable
end AspisR1.CuSavingsTryGraph
