import PV_LIB_SPEC_F361Entry
import PV_LIB_SPEC_ThreadContract
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F361Contract
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f361
abbrev ThreadMachine := PV_LIB_SPEC_ThreadMachine.Machine

/-- Literal provider inputs with the corrected thread step. Values is the
runtime-value channel, not a source-store transformer. This construction
establishes no runtime interpretation or source adequacy theorem. -/
def machine (x : Input) (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent) :
    ThreadMachine :=
  ⟨base x,x.K,x.P,handler x,x.resources,x.encode,values⟩

/-- Concrete additional entry-validity facet of COMMON. The descriptor and
layout come from the entry-selected registry, including empty references.
No later decoder, successful call or future store occurs here. -/
def RegisteredValidity (w : OWNER) : Prop :=
  ∀ p id h, w.places p = some id → PV_EVHB_RawVecOwner.lookup w.world id = some h →
    h.pointer ≠ 0 ∧ h.pointer % PV_EVHB_OwnerReserve.alignment h.shape.align = 0 ∧
    h.len ≤ h.cap ∧ h.pointer + h.cap*h.shape.width ≤ 2^64

/-- This is a compiled entry extension, with every provider representation
imported by name. It is not counted as the full frozen contract: the actual
capture/reference provenance and complete machine leaf inventory remain open. -/
def Pre (R : PV_LIB_SPEC_F361Entry.Representation) (x : Input) : Prop :=
  PV_LIB_SPEC_F361Entry.EntryComponent R x ∧ RegisteredValidity x.w

/-- The old source-step and arbitrary store-delta fields are preserved only
inside Input for comparison. The new reference does not execute either. -/
def reference (x : Input)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent) :=
  PV_LIB_SPEC_ThreadContract.reference (machine x values) (entry x)

/-- Explicit corrected behavioral target. This statement proves no row and
does not assert that old Post implies it. In particular no old successful-only
trace or relational child Post is installed as a deterministic graph. -/
def Post (x : Input)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadContract.BehavioralPost (machine x values) (entry x) candidate ∧
  ∀ n, PV_LIB_SPEC_ThreadContract.First (machine x values) (entry x) candidate n →
    (match (candidate n).current.status with
      | .fault .abort _ => True
      | _ => Frame x (candidate n) ∧ PV_LIB_SPEC_ThreadContract.Numbered (candidate n))

/-- A per-prefix comparison target against the package's EXISTING statement.
Its premise is the package's actual certificate type; its conclusion is
observational reachability in the corrected reference, without counter equality.
This is an obligation to prove, not a new MachineSpec/Pre field. -/
def PackageTransport (x : Input)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  ∀ q, Execution x (entry x) q →
    ∃ n, PV_LIB_SPEC_ThreadContract.observe (reference x values n) =
      PV_LIB_SPEC_ThreadContract.observe q

/-- Source/binary transport is separate from both entry validity and the
package comparison. No original-machine success is presumed. -/
def SourceAdequacy (x : Input)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (actual : Nat → State) : Prop :=
  PV_LIB_SPEC_ThreadContract.SourceAdequacy (machine x values) (entry x) actual

/-- Literal BEFORE/AFTER comparison at the actual typed provider boundary. -/
theorem pre_comparison (R : PV_LIB_SPEC_F361Entry.Representation) (x : Input) :
    Pre R x ↔ PV_FN_THREAD_f361.Pre x ∧
      PV_FN_THREAD_f361NameEntryValidity.EntryName R x ∧
      PV_FN_THREAD_f361ScopeEntryValidity.Shape x.scope ∧
      PV_LIB_SPEC_F361Entry.Numbered x ∧ RegisteredValidity x.w := by
  rw [Pre,PV_LIB_SPEC_F361Entry.before_after]
  constructor
  · rintro ⟨⟨old,label,scope,numbered⟩,valid⟩
    exact ⟨old,label,scope,numbered,valid⟩
  · rintro ⟨old,label,scope,numbered,valid⟩
    exact ⟨⟨old,label,scope,numbered⟩,valid⟩

theorem implies_package (R : PV_LIB_SPEC_F361Entry.Representation) (x : Input)
    (pre : Pre R x) : PV_FN_THREAD_f361.Pre x := pre.1.1.1

/-- The corrected reference retains the source-selected registration at14320.
This is a local model comparison, not a reachability assertion from entry. -/
theorem registration (x : Input)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    (PV_LIB_SPEC_ThreadMachine.step (machine x values)
      (PV_LIB_SPEC_RegistrationGap.before s a parents w es stack)).current.world.next =
        w.next+1 := PV_LIB_SPEC_ThreadMachine.registration _ _ _ _ _ _ _

#print axioms machine
#print axioms RegisteredValidity
#print axioms Pre
#print axioms reference
#print axioms Post
#print axioms PackageTransport
#print axioms SourceAdequacy
#print axioms pre_comparison
#print axioms implies_package
#print axioms registration
end PV_LIB_SPEC_F361Contract
