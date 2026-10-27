import RPu_FIx_SelectedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)

theorem value {N : Usize} (packed out : Array NQ 24#usize) (start : Usize) (a : Array NQ N)
    (model : Fin N.val → K) (same : decoded a=model)
    (positive : 0<N.val) (interval : start.val+N.val≤96)
    (hp : canonical packed) (ha : canonical a)
    (success : pool_v1.pair_forest_semantic_terminal.add_preweighted packed start a=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_SelectedMeaning.contribution model start.val j.val := by
  have source := FIx_PreweightedPointwise.value packed out start a positive interval hp ha success
  refine ⟨source.1,?_⟩
  intro j
  rw [source.2 j,FIx_SelectedMeaning.increment a model same start.val j.val]
#print axioms value
end AspisR1.FIx_PreweightedMeaning
end
