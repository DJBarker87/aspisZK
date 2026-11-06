import NLJ_ByteWindows
import NLC_CopyFrames
import NLJ_ObservedState
set_option autoImplicit false
namespace AspisR1.NLR_WindowFrame
open Aeneas Aeneas.Std AspisR1PublicPreparation
/-- Generic KMX partition over the ORIGINAL arbitrary memory, not a32-byte
restriction on the caller. This value law does not itself admit the physical
buffer projection of NLR's restricted native windows. -/
theorem partition {A : Type} (source target : Nat → A) (start count i : Nat) :
 KMX_CopyMeaning.loop source target start count i =
 if start ≤ i ∧ i < start+count then source i else target i :=
 KMX_CopyMeaning.loop_spec source target start count i
/-- Scalar/record frame chain for three ORIGINAL source windows. -/
theorem three_windows {A : Type} (p p0 p1 p2 : A)
 (first : p0=p) (second : p1=p0) (third : p2=p1) : p2=p :=
 third.trans (second.trans first)
/-- Every byte and extent is required; addresses never imply payload. -/
theorem prefix_fields (source actual : r1_wire.Prefix)
 (root : actual.c1_root = source.c1_root)
 (records : actual.records = source.records) : actual=source := by
 cases source
 cases actual
 cases root
 cases records
 rfl
#print axioms partition
#print axioms three_windows
#print axioms prefix_fields
end AspisR1.NLR_WindowFrame
