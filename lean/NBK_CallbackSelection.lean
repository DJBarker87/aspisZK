import SInt2_AcceptedPairClaims
import NBH_Audit
set_option autoImplicit false
noncomputable section
namespace NBK_CallbackSelection
open AspisR1

/-- The coherent installed SDK retains these slots from its input adapter.
This is a selection audit, not a native association or an installation. -/
theorem registry (base : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops) :
    (AspisS6CurrentFirstInstallation.install base ops).op25 = base.op25 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op26 = base.op26 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op27 = base.op27 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op28 = base.op28 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op29 = base.op29 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op30 = base.op30 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op31 = base.op31 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op32 = base.op32 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op33 = base.op33 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op34 = base.op34 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem policy_accounts (base : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops) :
    (AspisS6CurrentFirstInstallation.install base ops).op15 = base.op15 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op48 = base.op48 ∧
    (AspisS6CurrentFirstInstallation.install base ops).op49 = base.op49 := ⟨rfl,rfl,rfl⟩

#print axioms registry
#print axioms policy_accounts
end NBK_CallbackSelection
