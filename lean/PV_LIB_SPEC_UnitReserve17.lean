import PV_LIB_SPEC_Values14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_UnitReserve17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Pinned Rust1.94.1 alloc/src/raw_vec/mod.rs:601..603: a ZST's effective
capacity is usize::MAX even though RawVecInner.cap is ZERO_CAP (line43).
This instance is ONLY the retained F=Task=Unit specialization of Values14.
It does not infer ZST layout for an arbitrary fn10 instantiation. -/
def capacity (elementWidth stored : Nat) : Nat :=
  if elementWidth=0 then 2^64-1 else stored

/-- SPEC-C15 local correction for the Unit append10 branch. Source header
projections are still required. Non-ZST allocation/growth stays explicitly
partial through Values14; no returned RawVec or Store delta is accepted. -/
def reserve (p : Parameters) (fn buf : Data) (len extra : Nat)
    (w : OWNER) (r : Reply OWNER Event Data) : Option Data :=
  if PV_THR2_OffPath.functionId fn = some 10 then do
    let inner ← (runtime p).carrier.field buf 0
    let .number cap ← (runtime p).carrier.field inner 1 | none
    if len+extra ≤ capacity 0 cap then some buf else none
  else PV_LIB_SPEC_Values14.reserve p fn buf len extra w r

def values (p : Parameters) : PV_THR2_SourceStoreLibrary.Values OWNER Event :=
  {PV_LIB_SPEC_Values14.values p with reserve := reserve p}

/-- Checked counterexample to interpreting stored ZERO_CAP as ZST capacity.
This is a local header test, not a reached original append10 assertion. -/
theorem old_rejects_unit (p : Parameters) (fn : Data) (w : OWNER)
    (r : Reply OWNER Event Data) :
    (PV_LIB_SPEC_Values14.values p).reserve fn PV_LIB_SPEC_SpawnHooks14.raw 0 1 w r = none :=
  PV_LIB_SPEC_Values14.growth_gap p fn PV_LIB_SPEC_SpawnHooks14.raw
    (PV_THR2_KeyValues.pack PV_LIB_SPEC_HookKinds14.innerKind [.number 8,.number 0,.null])
    0 1 0 w r rfl rfl (by decide)

/-- Exact source projections plus usize overflow bound discharge this repaired
ZST case; no allocator success or decoded result is a hypothesis. -/
theorem unit_no_growth (p : Parameters) (fn buf inner : Data) (len extra cap : Nat)
    (w : OWNER) (r : Reply OWNER Event Data)
    (unitAppend : PV_THR2_OffPath.functionId fn = some 10)
    (buffer : (runtime p).carrier.field buf 0 = some inner)
    (stored : (runtime p).carrier.field inner 1 = some (.number cap))
    (bound : len+extra<2^64) :
    (values p).reserve fn buf len extra w r = some buf := by
  change reserve p fn buf len extra w r = _
  unfold reserve
  rw [if_pos unitAppend,buffer]
  change (do let .number n ← (runtime p).carrier.field inner 1 | none
             if len+extra ≤ capacity 0 n then some buf else none) = _
  rw [stored]
  exact if_pos (by dsimp [capacity]; omega)

theorem other_functions (p : Parameters) (fn buf : Data) (len extra : Nat)
    (w : OWNER) (r : Reply OWNER Event Data)
    (other : PV_THR2_OffPath.functionId fn ≠ some 10) :
    (values p).reserve fn buf len extra w r =
      (PV_LIB_SPEC_Values14.values p).reserve fn buf len extra w r := by
  change reserve p fn buf len extra w r = _
  exact if_neg other

#print axioms capacity
#print axioms reserve
#print axioms values
#print axioms old_rejects_unit
#print axioms unit_no_growth
#print axioms other_functions
end PV_LIB_SPEC_UnitReserve17
