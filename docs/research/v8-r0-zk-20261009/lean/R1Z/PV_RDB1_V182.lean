import R1Z.PV_RDB1_Append
import R1Z.PV_RDB1_ByteSlice
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V182

def nativeValue (s : alloc.vec.Vec U8) (t : Slice U8) : Result (alloc.vec.Vec U8) :=
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 s t

def ownedValue (s : alloc.vec.Vec U8) (t : Slice U8) : Result (alloc.vec.Vec U8) :=
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 s t

theorem complete (s : alloc.vec.Vec U8) (t : Slice U8) :
    nativeValue s t = ownedValue s t := rfl

/-- Preserve all representation-adapter errors; no invalid UTF8 or oversized
Lean String is silently admitted as a native String. -/
theorem adapter_complete (encode : String → Result (alloc.vec.Vec U8))
    (decode : alloc.vec.Vec U8 → Result String) (s : String) (t : Slice U8) :
    (do let bytes ← encode s; let bytes ← nativeValue bytes t; decode bytes) =
      (do let bytes ← encode s; let bytes ← ownedValue bytes t; decode bytes) := rfl

open PV_RDB1_V183_ReserveWorld
/-- Complete native reserve/copy/header/world law before panic/abort handling.
Applying the same deployed handler preserves its complete Result/effects. -/
theorem world_complete {S F R : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (tail : List U8)
    (w : World S F) (handler : PV_RDB1_Append.Appended S F → Result R) :
    handler (PV_RDB1_Append.source step wordMax byteMax shape b tail w) =
      handler (PV_RDB1_Append.reference step wordMax byteMax shape b tail w) :=
  congrArg handler (PV_RDB1_Append.complete step wordMax byteMax shape b tail w)

#print axioms complete
#print axioms adapter_complete
#print axioms world_complete
end R1Z.PV_RDB1_V182
