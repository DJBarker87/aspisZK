import NNG_ModelDecode
import NNG_LIBArrayDomain
import NGO_CanonicalPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DecodeReturned136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrayDomain
open AspisR1.NMT_Transport (arr)

theorem canonical (n : Usize) (r : r1_wire.ValidatedRecord) (off : Usize) (a : Array Q n)
    (success : NNG_ModelDecode.call n r off = .ok (.Ok a)) : DomainArray a := by
  have selected := NNG_ModelDecode.call_model n r off
  rw [success] at selected
  have native : AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain n (toT14 r) off =
      .ok (.Ok (arr toT1 a)) := selected.symm
  have good := AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain_success_members_canonical n (toT14 r) off _ native
  intro q member
  exact good (toT1 q) (List.mem_map.mpr ⟨q,member,rfl⟩)
#print axioms canonical
end AspisR1.NNG_DecodeReturned136
