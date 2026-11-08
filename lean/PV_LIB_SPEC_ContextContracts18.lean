import PV_LIB_SPEC_ContextF36118
import PV_LIB_SPEC_ContextF27018
import PV_LIB_SPEC_ContextF16618
import PV_LIB_SPEC_ContextF1518
import PV_LIB_SPEC_ContextF20818
import PV_LIB_SPEC_ContextF22018
import PV_LIB_SPEC_ContextF31618
import PV_LIB_SPEC_ContextF31818
import PV_LIB_SPEC_ContextF21918
import PV_LIB_SPEC_ContextF12518
import PV_LIB_SPEC_ContextF618
import PV_LIB_SPEC_ContextF17018
import PV_LIB_SPEC_ContextF1718
import PV_LIB_SPEC_ContextF518
import PV_LIB_SPEC_ContextF218
import PV_LIB_SPEC_ContextF118
import PV_LIB_SPEC_ContextF018
import PV_LIB_SPEC_ContextOwnInit18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextContracts18
open PV_STX_Machine PV_STX2_Syntax PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
/-- Data functions only. No native/Values/ownership proof is hidden here. -/
structure Implementations where
  f361 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF36118.Input → List Issued → List Context → Nat → Execution
  f270 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF27018.Input → List Issued → List Context → Nat → Execution
  f166 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF16618.Input → List Issued → List Context → Nat → Execution
  f15 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF1518.Input → List Issued → List Context → Nat → Execution
  f208 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF20818.Input → List Issued → List Context → Nat → Execution
  f220 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF22018.Input → List Issued → List Context → Nat → Execution
  f316 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF31618.Input → List Issued → List Context → Nat → Execution
  f318 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF31818.Input → List Issued → List Context → Nat → Execution
  f219 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF21918.Input → List Issued → List Context → Nat → Execution
  f125 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF12518.Input → List Issued → List Context → Nat → Execution
  f6 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF618.Input → List Issued → List Context → Nat → Execution
  f170 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF17018.Input → List Issued → List Context → Nat → Execution
  f17 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF1718.Input → List Issued → List Context → Nat → Execution
  f5 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF518.Input → List Issued → List Context → Nat → Execution
  f2 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF218.Input → List Issued → List Context → Nat → Execution
  f1 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF118.Input → List Issued → List Context → Nat → Execution
  f0 : PV_LIB_SPEC_ContextMachine18.Machine → PV_LIB_SPEC_ContextF018.Input → List Issued → List Context → Nat → Execution
  ownInit : PV_LIB_SPEC_ContextMachine18.Machine → OwnInit.Input → List Issued → List Context → Nat → Execution

/-- Exactly eighteen universal successor statements, all on ONE context/v2
machine, with the unchanged entry predicates and full source frame clauses.
This is not a proof that any implementations satisfy the conjunction. -/
def Contracts (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (R : F361.Representation) (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementations : Implementations) : Prop :=
  PV_LIB_SPEC_ContextF36118.Contract cut p R implementations.f361 ∧
  PV_LIB_SPEC_ContextF27018.Contract cut p implementations.f270 ∧
  PV_LIB_SPEC_ContextF16618.Contract cut p implementations.f166 ∧
  PV_LIB_SPEC_ContextF1518.Contract cut p implementations.f15 ∧
  PV_LIB_SPEC_ContextF20818.Contract cut p implementations.f208 ∧
  PV_LIB_SPEC_ContextF22018.Contract cut p implementations.f220 ∧
  PV_LIB_SPEC_ContextF31618.Contract cut p implementations.f316 ∧
  PV_LIB_SPEC_ContextF31818.Contract cut p implementations.f318 ∧
  PV_LIB_SPEC_ContextF21918.Contract cut p implementations.f219 ∧
  PV_LIB_SPEC_ContextF12518.Contract cut p implementations.f125 ∧
  PV_LIB_SPEC_ContextF618.Contract cut p implementations.f6 ∧
  PV_LIB_SPEC_ContextF17018.Contract cut p implementations.f170 ∧
  PV_LIB_SPEC_ContextF1718.Contract cut p implementations.f17 ∧
  PV_LIB_SPEC_ContextF518.Contract cut p implementations.f5 ∧
  PV_LIB_SPEC_ContextF218.Contract cut p implementations.f2 ∧
  PV_LIB_SPEC_ContextF118.Contract cut p implementations.f1 ∧
  PV_LIB_SPEC_ContextF018.Contract cut p implementations.f0 ∧
  PV_LIB_SPEC_ContextOwnInit18.Contract cut p granted implementations.ownInit

abbrev Before := PV_LIB_SPEC_Cut92Composition.Contracts

#print axioms Implementations
#print axioms Contracts
#print axioms Before
end PV_LIB_SPEC_ContextContracts18
