import PV_LIB_SPEC_F361Full
import PV_THR2_Intrinsic220ToInvoke
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F220Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- Whole own-entry Pre: source arguments, saved continuation, typed/registered
reference domain, OWNER validity and full live numbering. No future read,
Some branch, callee success, write-definedness or desired Post is assumed. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F220.live 2 r i
/-- Post_thread_f220: Unwrap the actual wrapper and invoke f208 at the source arguments; return its reply and effects.

Unwrap AssertUnwindSafe using its source aggregate, then invoke f208 with the same argument tuple; preserve callback effects and its exact nested Result.
The reference is the entire pinned body on the OWNER-aware D984 step, with
ONE completed action table parameter shared by every child. All exact nested
Result payloads, allocations before errors/logs, stop statuses, consumed
pending and divergence prefixes are retained. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F220.live i candidate
/-- Statement only; no row is proved or assumed CLOSED. -/
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

open PV_THR2_Intrinsic220ToInvoke
/-- Exact proposition of the package's PV_THR2_Intrinsic220ToInvoke.run,
source 41e76d01fdead952101594b8b0f36a7561d180f2. This is a PREFIX, not a previous whole contract.
Source SHA256 f21e0115f83f714e6f461c22ffbce8751c1db2d884cc978b3ff26ffd2280422c. -/
def PackageStatement : Prop := ∀ {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (kind payload : Data) (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,1,[]⟩ = some (PV_THR2_KeyValues.pack kind [payload])),
  PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      ctl programs handler (5+1)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F220.live.body},parents,s⟩,w,es⟩,stack⟩ =
    ⟨⟨.running (PV_THR2_Catch220Invoke.pending
      (PV_THR2_Catch220Prepare.afterStore s a kind payload) a parents payload),w,es⟩,stack⟩
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
end PV_LIB_SPEC_F220Full
