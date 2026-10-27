import LPa_Dot
import LPa_StageLaws
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Dot

theorem loop_length (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    (loop s a b).length = 4 := LPa.build_length _ _

theorem model_total (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    fast_pairing.canonical.Dot.push s a b = ok ⟨⟨loop s a b,loop_length s a b⟩⟩ := by
  rw [shipped_leaf_model, dif_pos (loop_length s a b)]
-- This exposes the exact existing model boundary: no canonicality check lives
-- in Dot.push itself. Native canonical Q producers still need their own join.
#print axioms loop_length
#print axioms model_total
end LPa.Dot
