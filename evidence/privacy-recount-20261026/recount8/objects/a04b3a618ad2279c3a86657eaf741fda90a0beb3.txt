import R1Z.PV_RunJoin_JoinedInstallation
import R1Z.PV_RunJoin_SourceSelectionContract
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_JoinedFamily
open Aeneas Aeneas.Std Result ProverRwFull
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1
local notation "K" => PrivacyR1AcctBasis.K
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {CommitHandle N C : Type}

def inputs (base : ExternalTypes)
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle)
    (h : HonestProver K) (x : Statement K CommitHandle) (w : h.Instance) :=
  PV_Join_FixtureInputs.inputs base ops (hash x) (selection.selected h x w)

def common (base : ExternalTypes)
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle) (x : Statement K CommitHandle) :=
  PV_Join_FixtureInputs.inputs base ops (hash x) (selection.publicRecord x)

theorem identity (base : ExternalTypes)
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle)
    (h : HonestProver K) (x : Statement K CommitHandle) (w : h.Instance)
    (s : PV_Join_LedgerSource.World base N C) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    PV_RunJoin_MapErrInstalled.Identity ((inputs base ops hash selection h x w).ops s) :=
  PV_RunJoin_JoinedInstallation.installed_identity base ops (hash x) _ s

/-- Source public binding stays a P obligation on the SAME selected record. -/
theorem public_common (base : ExternalTypes)
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle)
    (binding : PV_RunJoin_InstalledFamily.PublicBinding selection)
    (h : HonestProver K) (x : Statement K CommitHandle) (w : h.Instance)
    (hw : h.public w = x.1) (s : PV_Join_LedgerSource.World base N C) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    (inputs base ops hash selection h x w).ops s = (common base ops hash selection x).ops s ∧
    (inputs base ops hash selection h x w).pub s = (common base ops hash selection x).pub s ∧
    (inputs base ops hash selection h x w).hash s = (common base ops hash selection x).hash s :=
  PV_RunJoin_JoinedInstallation.common_public base ops (hash x) _ _ (binding h x w hw) s

#print axioms identity
#print axioms public_common
end R1Z.PV_RunJoin_JoinedFamily
