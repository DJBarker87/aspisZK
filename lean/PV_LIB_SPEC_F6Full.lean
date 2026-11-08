import PV_LIB_SPEC_F125Full
import PV_FN_THREAD_f6Joins
import PV_FN_THREAD_f6EntryNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F6Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Representation adapter only; no run, output or cross-callee counter
comparison. Every field is the literal provider entry field. -/
def packageInput (i : Input) : PV_FN_THREAD_f6Interfaces.Entry Event :=
  ⟨i.activation,PV_THR2_F6.live,i.store,i.parent,i.parents,i.waiting,
    i.destination,i.arguments,i.world,i.events,i.suspended⟩
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F6.live 1 r i ∧
  ∃ (F Task : Type) (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task)
    (callback : Data), PV_FN_THREAD_f6.Pre' (packageInput i) captures callback
/-- Construct both actual Arc counts; execute the real catch/callback and
completion/park loop with every response retained. Return the source Ok payload,
preserve Err/panic/abort/pending/divergence. No eventual-zero or successful
callee premise; no obligations extend into lower caller code after delivery. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F6.live i candidate
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)
abbrev PackagePre := @PV_FN_THREAD_f6.Pre'
abbrev PackagePost := @PV_FN_THREAD_f6Joins.Post
abbrev PackageContract := @PV_FN_THREAD_f6.Contract
/-- Literal old typed contract (original interpreter with named125 dependency)
and the new corrected-machine contract remain distinct statements. PrefixIdentity,
GlobalOriginalTransport and loop joins are old proof targets, not new premises. -/
def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ i, Pre r i → ∃ (F Task : Type)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : Data),
    PV_FN_THREAD_f6.Pre' (packageInput i) captures callback) ∧
  Contract table r implementation
#print axioms MachineSpec
#print axioms packageInput
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackagePre
#print axioms PackagePost
#print axioms PackageContract
#print axioms Comparison
end PV_LIB_SPEC_F6Full
