import R1Z.PDict_MoreCarriers
import R1Z.ProverRwRngTransportValidity
set_option autoImplicit false
namespace R1Z.PDict_ErrorCarrier
open Aeneas Aeneas.Std ProverRwFull

/-- Complete value view of Linux getrandom::Error under the existing P6
raw-code codec: every nonzero signed32-bit value, including native boundaries.
This binds values only; callback histories, E1, ABI/Drop composition stay open. -/
structure ErrorValue where
  code : {i : I32 // i.val ≠ 0}

def encode (i : {i : I32 // i.val ≠ 0}) : ErrorValue := ⟨i⟩
def decode (e : ErrorValue) : {i : I32 // i.val ≠ 0} := e.code

theorem decode_encode (i : {i : I32 // i.val ≠ 0}) : decode (encode i) = i := rfl

theorem encode_decode (e : ErrorValue) : encode (decode e) = e := by cases e; rfl

theorem exact_pattern (e : ErrorValue) : ProverRwRngTransportValidity.Pattern e.code.val :=
  (ProverRwRngTransportValidity.pattern_iff_nonzero e.code.val).mpr e.code.property

@[reducible] def native (base : ExternalTypes) : ExternalTypes :=
  { PDict_MoreCarriers.native base with op7 := ErrorValue }

theorem type7 (base : ExternalTypes) : (native base).op7 = ErrorValue := rfl

theorem carrier_retraction (base : ExternalTypes) :
    PDict_MoreCarriers.native (native base) = native base := rfl

@[reducible] noncomputable def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  @PDict_MoreCarriers.selected (native base) ops

#print axioms decode_encode
#print axioms encode_decode
#print axioms exact_pattern
#print axioms type7
#print axioms carrier_retraction
end R1Z.PDict_ErrorCarrier
