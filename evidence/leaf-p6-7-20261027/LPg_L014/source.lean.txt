import LPa_Map
import XRk_DotModel
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Dot
-- Native bridge: fast_pairing::canonical::LPa_dot::LPa_dot_stage (K017).
-- The native raw producer is shared in K017; XRk_raw/native raw binding is OPEN.
def step (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) (i : Nat) : U64 :=
  XRk_u64 ((s.sums.val[i]?.getD 0#u64).val + XRk_partial ((XRk_raw a b)[i]?.getD 0))
def loop (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) : List U64 :=
  LPa.build (step s a b) 4

theorem loop_eq_map (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    loop s a b = (List.range 4).map (step s a b) := LPa.build_map _ _
theorem loop_eq_fold (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    loop s a b = (List.range 4).foldl (fun xs i => xs ++ [step s a b i]) [] := LPa.build_fold _ _
theorem shipped_leaf_model (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    fast_pairing.canonical.Dot.push s a b =
      if h : (loop s a b).length = 4 then ok ⟨⟨loop s a b,h⟩⟩ else fail .panic := by
  simp only [loop_eq_map]
  rfl
#print axioms loop_eq_map
#print axioms loop_eq_fold
#print axioms shipped_leaf_model
end LPa.Dot
