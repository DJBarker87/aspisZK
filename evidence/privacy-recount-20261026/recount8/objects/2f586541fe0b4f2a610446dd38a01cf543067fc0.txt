import R1Z.PV_RDB2_LayoutGuards
import R1Z.PV_RDB2_ConstructorEffects

/-! Complete transport of the changed Global allocation wrappers. The same
allocator hooks and complete effects occur in the same order in both bodies.
This is not a proof that an arbitrary allocator hook provides fresh memory;
that remains a separate concrete resource-family association. -/
namespace R1Z.PV_RDB2_GlobalAlloc
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_LayoutGuards PV_RDB2_ConstructorEffects

def oldAlloc {World : Type} (shim : World → Result World)
    (allocate : Nat → Nat → World → Result (Raw × World))
    (layout : Layout) (world : World) : Result (Raw × World) := do
  let world ← shim world
  allocate layout.size layout.align world

def deployedAlloc {World : Type} (shim : World → Result World)
    (allocate : Nat → Nat → World → Result (Raw × World))
    (layout : Layout) (world : World) : Result (Raw × World) := do
  let world ← shim world
  allocate layout.size layout.align world

theorem allocate_complete {World : Type} (shim : World → Result World)
    (allocate : Nat → Nat → World → Result (Raw × World))
    (layout : Layout) (world : World) :
    oldAlloc shim allocate layout world = deployedAlloc shim allocate layout world := rfl

def castSlice (ptr : Raw) (size : Nat) : Raw := {ptr with metadata := some size}
def sliceFromRawParts (ptr : Raw) (size : Nat) : Raw :=
  ⟨ptr.allocation,ptr.address,some size⟩

def oldGlobal {World : Type} (allocate zero : Layout → World → Result (Raw × World))
    (layout : Layout) (zeroed : Bool) (world : World) :
    Result (Except Unit Raw × World) :=
  if layout.size = 0 then ok (.ok (castSlice ⟨none,layout.align,none⟩ 0),world)
  else do
    let (ptr,world) ← if zeroed then zero layout world else allocate layout world
    if ptr.address = 0 then ok (.error (),world)
    else ok (.ok (castSlice ptr layout.size),world)

def deployedGlobal {World : Type} (allocate zero : Layout → World → Result (Raw × World))
    (layout : Layout) (zeroed : Bool) (world : World) :
    Result (Except Unit Raw × World) :=
  if layout.size = 0 then ok (.ok (sliceFromRawParts ⟨none,layout.align,none⟩ 0),world)
  else do
    let (ptr,world) ← if zeroed then zero layout world else allocate layout world
    if ptr.address = 0 then ok (.error (),world)
    else ok (.ok (sliceFromRawParts ptr layout.size),world)

theorem runtime_complete {World : Type} (allocate zero : Layout → World → Result (Raw × World))
    (layout : Layout) (zeroed : Bool) (world : World) :
    oldGlobal allocate zero layout zeroed world = deployedGlobal allocate zero layout zeroed world := rfl

theorem zero_no_allocator_call {World : Type} (allocate zero : Layout → World → Result (Raw × World))
    (align : Nat) (zeroed : Bool) (world : World) :
    deployedGlobal allocate zero ⟨0,align⟩ zeroed world =
      ok (.ok ⟨none,align,some 0⟩,world) := by
  simp only [deployedGlobal,↓reduceIte,sliceFromRawParts]

theorem null_is_allocation_error {World : Type}
    (allocate zero : Layout → World → Result (Raw × World))
    (layout : Layout) (zeroed : Bool) (world after : World) (ptr : Raw)
    (nonzero : layout.size ≠ 0) (null : ptr.address = 0)
    (call : (if zeroed then zero layout world else allocate layout world)=ok (ptr,after)) :
    deployedGlobal allocate zero layout zeroed world = ok (.error (),after) := by
  cases zeroed with
  | false =>
    have hc : allocate layout world = ok (ptr,after) := by simpa using call
    simp [deployedGlobal,nonzero,hc,null]
  | true =>
    have hc : zero layout world = ok (ptr,after) := by simpa using call
    simp [deployedGlobal,nonzero,hc,null]

#print axioms allocate_complete
#print axioms runtime_complete
#print axioms zero_no_allocator_call
#print axioms null_is_allocation_error
end R1Z.PV_RDB2_GlobalAlloc
