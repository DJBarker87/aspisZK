import R1Z.PV_RDB2C_PV_RDB1_V183
import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Reserve
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View
open PV_RDB1_V183_ReserveWorld
/-- Consume the existing complete reserve law rather than proving a new
success-only reserve, or assuming allocation succeeds. -/
theorem complete {T S F : Type} (step : Request → S → Option Nat × S)
 (wordMax byteMax : Nat) (shape : Shape) (buffer : Buffer T) (additional : Nat)
 (world : World S F) : native step wordMax byteMax shape buffer additional world=
 reference step wordMax byteMax shape buffer additional world :=
 PV_RDB1_V183.complete step wordMax byteMax shape buffer additional world

/-- Connect the reserve family's byte-prefix law to the typed initialized-byte
carrier. Padding/unknown bytes remain Option values; no logical-cell store is
substituted for byte initialization. -/
theorem initialized_prefix (request : Request) (memory : Nat → Option Nat) (c : Cell)
 (destination : Nat) (grow:request.oldCapacity≤request.newCapacity)
 (size:c.size=request.oldCapacity*request.shape.width)
 (association:∀ i, i<c.size → memory (request.address+i)=(c.contents i).map UInt8.toNat)
 (i : Nat) (inside:i<c.size) :
 memoryAfter request destination memory (destination+i)=(c.contents i).map UInt8.toNat := by
 rw [copied_prefix request memory destination i grow (by omega)]
 exact association i inside

/-- A typed object's exact byte representation survives successful growth,
provided the native source-to-byte association has been discharged. -/
theorem typed_prefix {T : Type} (codec : Codec T) (request : Request)
 (memory : Nat → Option Nat) (c : Cell) (destination offset : Nat) (v : T)
 (grow:request.oldCapacity≤request.newCapacity)
 (size:c.size=request.oldCapacity*request.shape.width)
 (association:∀ i, i<c.size → memory (request.address+i)=(c.contents i).map UInt8.toNat)
 (repr:Represents codec c offset v) (i : Nat) (hi:i<codec.width) :
 memoryAfter request destination memory (destination+(offset+i))=(codec.encode v i).map UInt8.toNat := by
 have hin:offset+i<c.size := by have hh:=repr.1; unfold Fits at hh; omega
 rw [initialized_prefix request memory c destination grow size association (offset+i) hin,repr.2 i hi]
#print axioms complete
#print axioms initialized_prefix
#print axioms typed_prefix
end R1Z.PV_OWN_Reserve
