import NNH_HostExec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostClockFinding
open Aeneas Aeneas.Std AspisR1 S2Trust S2W_D189Entry NNH_HostCtx
/-- This is a representation finding, not a counterexample to A2 itself:
current EnvRep fixes fx.clock independently of the selected j.slot. -/
def different {W Tx : Type} (c : Ctx W Tx) : Ctx W Tx :=
 {c with fixed := {c.fixed with clock := .ok 0},j := {c.j with slot := .Ok 1#u64}}

theorem mismatch {W Tx : Type} (c : Ctx W Tx) :
 (envOf (different c)).clock ≠ NND_Carrier.reply NND_Carrier.slot (different c).j.slot := by
 decide

theorem admitted_environment {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : Ctx W Tx) :
 (NNH_LiteralHost.S_host L copy std).Exhibited (different c) ∧
 (NNH_LiteralHost.S_host L copy std).EnvRep (different c) (envOf (different c)) ∧
 (envOf (different c)).clock ≠ NND_Carrier.reply NND_Carrier.slot (different c).j.slot :=
 ⟨rfl,NNH_HostEnv.environment_rep _ _ _ _,mismatch c⟩
#print axioms mismatch
#print axioms admitted_environment
end AspisR1.NNH_HostClockFinding
end
