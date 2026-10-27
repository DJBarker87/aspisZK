import LPc_DecodeCanonical
open Aeneas Aeneas.Std Result XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPc.Decode
/-- Relates every indexed native-model stage to the symbolic generated list. -/
theorem values_get (payload : List U8) (start n i : Nat) (bound : i < n) :
    (LPa.Decode.values payload start n)[i]?.getD (true,qzero) =
      LPa.Decode.step payload start i := by
  rw [LPa.Decode.values_eq_map]
  simp [bound]
/-- Canonicality is derived from accepted decoding flags at arbitrary length. -/
theorem values_canonical (payload : List U8) (start n : Nat)
    (accepted : LPa.firstBad
      (fun j => !((LPa.Decode.values payload start n)[j]?.getD (true,qzero)).1) n = none) :
    ∀ q ∈ (LPa.Decode.values payload start n).map Prod.snd, LPa.Add.Canonical q := by
  intro q hq
  rw [LPa.Decode.values_eq_map, List.map_map] at hq
  rcases List.mem_map.mp hq with ⟨i,hi,rfl⟩
  have bound := List.mem_range.mp hi
  apply step_canonical
  have good := LPa.Decode.accepted_values payload start n accepted i bound
  rw [values_get payload start n i bound] at good
  exact good
#print axioms values_get
#print axioms values_canonical
end LPc.Decode
