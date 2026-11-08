import PV_LIB_SPEC_PrefixNative14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Values14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
/-- Prefix instance for F=Task=Unit. Emitted9 iterates Result<Vec<Unit>,
Box<dyn Any+Send>> or ScopedJoinHandle thereof, both24 bytes in the adopted
ELF;167 pushes those same24-byte elements.10 appends Unit (width0).
Only9 uses width in the supplied v2 implementation. Other ids return0;
this is an explicitly scoped instance, not arbitrary-type layout reflection. -/
def width (fn : Data) : Nat := match PV_THR2_OffPath.functionId fn with
  | some 9 | some 167 => 24
  | _ => 0
/-- Opaque NonNull is the retained numeric physical-pointer facet. Preserve
it under arithmetic; reject unknown/invalid representations instead of
returning an invented null or dropping a provenance-bearing source tag. -/
def rawNonNull : Data → Option Data
  | .number n => if 0<n ∧ n<2^64 then some (.number n) else none
  | _ => none
def addNonNull (v : Data) (offset : Nat) : Option Data := do
  let .number n ← rawNonNull v | none
  if n+offset<2^64 then some (.number (n+offset)) else none
def subPointer (v : Data) (offset : Nat) : Option Data := do
  let .number n ← rawNonNull v | none
  if offset<n then some (.number (n-offset)) else none

/-- RawVec's finite source header is read through the actual carrier. This
binds the no-growth case exactly. A required grow remains None: the native
allocator/copy binding is not smuggled in via r.answer or a Store transformer.
Every non-success arm is handled by the retained v2 table before reserve. -/
def reserve (p : Parameters) (_fn buf : Data) (len extra : Nat)
    (_w : OWNER) (_r : Reply OWNER Event Data) : Option Data := do
  let inner ← (runtime p).carrier.field buf 0
  let .number cap ← (runtime p).carrier.field inner 1 | none
  if len+extra≤cap ∧ len+extra<2^64 then some buf else none

def values (p : Parameters) : PV_THR2_SourceStoreLibrary.Values OWNER Event :=
  ⟨width,rawNonNull,addNonNull,subPointer,reserve p⟩

theorem no_growth (p : Parameters) (fn buf inner : Data) (len extra cap : Nat)
    (w : OWNER) (r : Reply OWNER Event Data)
    (buffer : (runtime p).carrier.field buf 0 = some inner)
    (capacity : (runtime p).carrier.field inner 1 = some (.number cap))
    (fits : len+extra≤cap) (bound : len+extra<2^64) :
    (values p).reserve fn buf len extra w r = some buf := by
  change reserve p fn buf len extra w r = _
  unfold reserve
  rw [buffer]
  change (do let Data.number n ← (runtime p).carrier.field inner 1 | none
             if len+extra≤n ∧ len+extra<2^64 then some buf else none) = _
  rw [capacity]
  exact if_pos ⟨fits,bound⟩

theorem growth_gap (p : Parameters) (fn buf inner : Data) (len extra cap : Nat)
    (w : OWNER) (r : Reply OWNER Event Data)
    (buffer : (runtime p).carrier.field buf 0 = some inner)
    (capacity : (runtime p).carrier.field inner 1 = some (.number cap))
    (grow : cap<len+extra) :
    (values p).reserve fn buf len extra w r = none := by
  change reserve p fn buf len extra w r = _
  unfold reserve
  rw [buffer]
  change (do let Data.number n ← (runtime p).carrier.field inner 1 | none
             if len+extra≤n ∧ len+extra<2^64 then some buf else none) = _
  rw [capacity]
  exact if_neg (by omega)

theorem hooks_empty (p : Parameters) (fn : Data) (w : OWNER) (r : Reply OWNER Event Data) :
    (values p).reserve fn PV_LIB_SPEC_SpawnHooks14.raw 0 0 w r =
      some PV_LIB_SPEC_SpawnHooks14.raw :=
  no_growth p _ _ _ 0 0 0 w r rfl rfl (by decide) (by decide)

#print axioms width
#print axioms rawNonNull
#print axioms addNonNull
#print axioms subPointer
#print axioms reserve
#print axioms values
#print axioms no_growth
#print axioms growth_gap
#print axioms hooks_empty
end PV_LIB_SPEC_Values14
