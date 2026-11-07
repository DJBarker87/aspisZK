import NNG_LIBArrays
import NNG_Transport_T14
import NNG_Root32
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBData
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport

abbrev transcript := @toT10 Unit
abbrev point := toT2
abbrev record := toT14
abbrev error := toT13
abbrev bytes := LIB_Carriers.bytes
abbrev b32 := LIB_Carriers.b32

def lowerPrefix (p : LIB_VCarriers.Prefix) : NNG_verify_finish.r1_wire.Prefix :=
  fromT12 (LIB_VCarriers.prefixRaw p)
def lowerPublic (p : LIB_VCarriers.Public) : Public := fromT9 p

theorem prefix_exact (p : LIB_VCarriers.Prefix) :
    toT12 (lowerPrefix p) = LIB_VCarriers.prefixRaw p := fromT12_inverse _
#print axioms prefix_exact

theorem public_exact (p : LIB_VCarriers.Public) : toT9 (lowerPublic p) = p := fromT9_inverse _
#print axioms public_exact

theorem point_injective : Function.Injective point := by
  intro x y same
  have h := congrArg fromT2 same
  simpa only [toT2_inverse] using h
#print axioms point_injective

theorem c1Root (p : LIB_VCarriers.Prefix) :
    LIB_VCarriers.c1Root p = b32 (lowerPrefix p).c1_root := rfl
#print axioms c1Root

theorem state (t : NNG_verify_finish.r1_wire.SemanticTranscript Unit) :
    LIB_VCarriers.state (transcript t) = b32 t.state := rfl
#print axioms state

theorem bytes_length (s : Slice U8) : (bytes s).length = s.val.length := by
  change (NNC_ByteCarriers.host s.val).length = s.val.length
  simp [NNC_ByteCarriers.host]
#print axioms bytes_length

theorem root_bytes (s : Slice U8) (h : s.val.length = 32) :
    (b32 (NNG_Root32.value s h)).bytes = bytes s := rfl
#print axioms root_bytes
end AspisR1.NNG_LIBData
