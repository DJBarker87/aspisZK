import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_VariantGuard
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes]
/-- The three-constructor equality. Its installation into runjoin's actual
opsNative remains a named obligation, rather than an assumed dictionary fact. -/
def equal : transport.Variant → transport.Variant → Result Bool
  | .S1,.S1 => .ok true
  | .S2,.S2 => .ok true
  | .D,.D => .ok true
  | _,_ => .ok false

def install (ops : ExternalFuns) : ExternalFuns := {ops with op233 := equal}

def guard (v : transport.Variant) : P Bool :=
  pure (match v with | .S2 => false | _ => true)

theorem equal_exact (a b : transport.Variant) : equal a b = .ok true ↔ a = b := by
  cases a <;> cases b <;> simp only [equal,Result.ok.injEq,reduceCtorEq,true_iff,not_false_eq_true]

theorem guard_fixed (ops : ExternalFuns) (v : transport.Variant) :
    letI : ExternalFuns := install ops
    FinishedView (guard v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v .S2) := by
  letI : ExternalFuns := install ops
  cases v with
  | S1 => exact PV_EVH_Prefix.lift_fixed (.ok true)
  | S2 => exact PV_EVH_Prefix.lift_fixed (.ok false)
  | D => exact PV_EVH_Prefix.lift_fixed (.ok true)

theorem terminal (v : transport.Variant) (w : World) :
    guard v w = ⟨.finished (.ok (match v with | .S2 => false | _ => true)),w,[]⟩ := rfl
#print axioms equal_exact
#print axioms guard_fixed
#print axioms terminal
end PV_EVH_VariantGuard
