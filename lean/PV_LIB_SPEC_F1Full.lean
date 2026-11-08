import PV_LIB_SPEC_F361Full
import PV_FN_THREAD_f1Entry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F1Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F1.live 3 r i ∧ ∃ n f flag, i.arguments = [.number n,f,flag] ∧ n < 2^64 ∧ ∃ b, r.carrier.truth flag = some b
/-- Post_thread_f1: Follow the source worker/sequential branch, scope, spawn and join order and return ordered results; preserve entry capture ownership with exact handle/worker effects.

Both worker/sequential routes remain in the domain. Iterate and collect at source arguments; retain order of scope/spawn/join and append. Native iterator f9 and Vec append f10 update their SOURCE descriptors through the concrete store-action interpreter. Resource demand witness independence is an obligation to prove, not an entry restriction.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F1.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_FN_THREAD_f1Entry
/-- Exact proposition of the package's PV_FN_THREAD_f1Entry.prepare,
source 18ca5e54ca03ee8b65a9838b1562b2fc1df6798c. This is a PREFIX, not a previous whole contract.
Source SHA256 742b70f621ee8229d45bdcd62629ebc6de69a3d606392e1b722760260b55d84b. -/
def PackageStatement : Prop := ∀ {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (n : Data)
    (w : W) (es : List E) (stack : List Config)
    (nCell : s.cells ⟨a,1,[]⟩ = some n),
  PV_THR2_IntrinsicState.advance B K P H 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 6},parents,
        prepared s a n⟩,w,es⟩,stack⟩
/-- Explicit side-by-side obligations. No implication, equivalence or proof
of the new whole contract is inferred from the package's prefix theorem. -/
def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PackageStatement ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F1Full
