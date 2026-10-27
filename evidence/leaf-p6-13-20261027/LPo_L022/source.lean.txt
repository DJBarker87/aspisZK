import LPo_B_LPc_DecodeCanonical
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.BC.Decode
/-- Relates every indexed native-model stage to the symbolic generated list. -/
theorem values_get (payload : List U8) (start n i : Nat) (bound : i < n) :
    (LPo.BA.Decode.values payload start n)[i]?.getD (true,qzero) =
      LPo.BA.Decode.step payload start i := by
  rw [LPo.BA.Decode.values_eq_map]
  simp [bound]
/-- Canonicality is derived from accepted decoding flags at arbitrary length. -/
theorem values_canonical (payload : List U8) (start n : Nat)
    (accepted : LPo.BA.firstBad
      (fun j => !((LPo.BA.Decode.values payload start n)[j]?.getD (true,qzero)).1) n = none) :
    ∀ q ∈ (LPo.BA.Decode.values payload start n).map Prod.snd, LPo.BA.Add.Canonical q := by
  intro q hq
  rw [LPo.BA.Decode.values_eq_map, List.map_map] at hq
  rcases List.mem_map.mp hq with ⟨i,hi,rfl⟩
  have bound := List.mem_range.mp hi
  apply step_canonical
  have good := LPo.BA.Decode.accepted_values payload start n accepted i bound
  rw [values_get payload start n i bound] at good
  exact good
#print axioms values_get
#print axioms values_canonical
end LPo.BC.Decode
