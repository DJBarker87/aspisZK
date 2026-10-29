import PV_B3Q_MatrixStore
import PV_B3Q_MatrixEntries
import PV_B3P_MatrixTrace14227
namespace PV_B3Q_Matrix
open Aeneas Aeneas.Std PV_B3P_Binding14227
set_option autoImplicit false
/-- Every bounded source-store prefix, observed as all nine words, agrees with
its model prefix. The native arithmetic supplying each word is a separate row. -/
theorem observed_prefixes (writes : List Write14) (sums : Matrix14)
    (bound : MatrixWritesBound14 writes) :
    (do let states ← matrix_trace14 deployed_store writes sums
        .ok (states.map entries)) =
    (do let states ← matrix_trace14 model_matrix_store14 writes sums
        .ok (states.map entries)) := by
  have same : deployed_store = source_matrix_store14 := rfl
  rw [same,matrix_trace_binding14 writes sums bound]
/-- Joint witness: the exact same store port satisfies the standing matrix link,
and complete raw observations distinguish any two matrix states. -/
theorem matrix_link_and_observation :
    PV_B3P_Link_matrix_stores deployed_store ∧
      (∀ a b : Matrix14, entries a = entries b → a = b) :=
  ⟨deployed_store_link, entries_injective⟩
#print axioms observed_prefixes
#print axioms matrix_link_and_observation
end PV_B3Q_Matrix
