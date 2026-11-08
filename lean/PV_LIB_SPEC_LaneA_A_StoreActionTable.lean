import PV_LIB_A_DropDispatchV2
set_option autoImplicit false
noncomputable section

/- Import surface for the supplied v2 source-store projections. This is a
PARTIAL table: its name does not certify the unimplemented wrapper/destructor
semantics. In particular bool-only504 and nonlast486/683 remain restricted.
The source adequacy status is exposed by `coverage`, not erased by this API. -/
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary

inductive Action where
  | legacy (f : PV_THR2_SourceStoreNative.Function)
  | primitive (f : PV_LIB_A_StoreDispatchV2.Function)
  | scopeIncrement457 | scopeDecrement611 | cellTake641 | cellBoolSet504
  | arcNonlast486 | weakNonlast683 | optionTake369

/-- Each supplied function has exactly one entry. The incorrect wrapped Cell
and bool-data AtomicBool drafts are unreachable through this definition.
An absent entry denotes MISSING coverage, never a proved no-write function. -/
def v2 (fn : Data) : Option Action :=
  match PV_THR2_OffPath.functionId fn with
  | some 504 => some .cellBoolSet504
  | some 641 => some .cellTake641
  | some 457 => some .scopeIncrement457
  | some 611 => some .scopeDecrement611
  | some 486 => some .arcNonlast486
  | some 683 => some .weakNonlast683
  | some 369 => some .optionTake369
  | _ => match PV_LIB_A_StoreDispatchV2.function fn with
    | some f => some (.primitive f)
    | none => (PV_THR2_SourceStoreNative.function fn).map Action.legacy

inductive Coverage where
  | directProjection | boolOnly | nonlastOnly | unparkCompositionOpen
  deriving DecidableEq

def coverage : Action → Coverage
  | .cellBoolSet504 => .boolOnly
  | .arcNonlast486 | .weakNonlast683 => .nonlastOnly
  | .scopeDecrement611 => .unparkCompositionOpen
  | _ => .directProjection

/-- A fixed dispatch over the named meanings. `values` is the existing W4
VALUE-only environment; this API introduces no Store transformer or law field.
The complete reply is an input to the deterministic projection and is passed
unchanged to delivery by the companion interpreter. -/
def interpret {W E : Type} (C : Carrier W Data) (values : Values W E)
    (action : Action) (fn : Data) (args : List Data) (s : Store Data)
    (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match action with
  | .legacy f => PV_THR2_SourceStoreLibrary.interpret C values f fn args s w r
  | .primitive f => PV_LIB_A_StoreDispatchV2.interpret C f args s w r
  | .scopeIncrement457 => PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 C args s w
  | .scopeDecrement611 => PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611 C args s w
  | .cellTake641 => PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellTake641 C args s w
  | .cellBoolSet504 => PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellBoolSet504 C args s w
  | .arcNonlast486 => PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_ArcDropNonlast486 C args s w
  | .weakNonlast683 => PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_WeakDropNonlast683 C args s w
  | .optionTake369 => PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_OptionTake369 C args s w

/-- The weak-CAS error arm (including spurious failure) is selected by the
returned Rust Result discriminant; it is not forced to succeed when equal. -/
theorem weak_cas {W E : Type} (C : Carrier W Data) (values : Values W E)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) :
    interpret C values (.primitive .cas530) fn args s w r =
      PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchangeWeak530 C args s w r := rfl

theorem strong_cas {W E : Type} (C : Carrier W Data) (values : Values W E)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) :
    interpret C values (.primitive .cas555) fn args s w r =
      PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchange555 C args s w r := rfl

/-- Arc clone's increment-before-overflow-abort is retained for EVERY reply,
without imposing success or an overflow-free count as an interface premise. -/
theorem clone_all_answers {W E : Type} (C : Carrier W Data) (values : Values W E)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) :
    interpret C values (.primitive .arcClone360) fn args s w r =
      PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360 C args s w := rfl

theorem scope_overflow {W E : Type} (C : Carrier W Data) (values : Values W E)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) :
    interpret C values .scopeIncrement457 fn args s w r =
      PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 C args s w := rfl

#print axioms v2
#print axioms coverage
#print axioms interpret
#print axioms weak_cas
#print axioms strong_cas
#print axioms clone_all_answers
#print axioms scope_overflow
end PV_LIB_StoreActionTable
