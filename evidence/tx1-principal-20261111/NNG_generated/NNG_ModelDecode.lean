import NNG_InstallBase
import NNG_EmittedContext
import NGO_CanonicalPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelDecode
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
open AspisR1.NMT_Transport (arr arr_inverse)

def call (n : Usize) (r : r1_wire.ValidatedRecord) (off : Usize) :=
  outer (inner (arr fromT1) fromT13)
    (AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain n (toT14 r) off)

theorem call_model (n : Usize) (r : r1_wire.ValidatedRecord) (off : Usize) :
    outer (inner (arr toT1) toT13) (call n r off) =
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain n (toT14 r) off := by
  apply outer_inverse
  intro reply
  apply inner_inverse (arr fromT1) (arr toT1) fromT13 toT13
  · exact arr_inverse fromT1 toT1 fromT1_inverse
  · exact fromT13_inverse
#print axioms call_model
end AspisR1.NNG_ModelDecode
