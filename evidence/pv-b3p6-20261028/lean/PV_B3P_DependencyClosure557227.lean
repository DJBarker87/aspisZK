import PV_B3Q_PartialCatalogue2
import PV_B3Q_D188
import PV_B3Q_MatrixStore
import PV_B3Q_FourSlice
import PV_B3P_FieldsVecState15227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3P_Binding14227
open PV_B3P_Fields15227 PV_B3P_Binding13227
set_option autoImplicit false
/-- A disjoint extension of b3q2's five-entry catalogue, at exact port types.
Matrix coordinates are restricted to the already stated store-link domain.
Fields retain the Vec carrier, including its size invariant and partial state.
This is a PARTIAL catalogue: it makes no whole-caller coverage assertion. -/
inductive Port557 where
  | dependency (body : PV_B3Q_PartialCatalogue2.Body)
  | store | matrix | slice | fields

abbrev MatrixIndex557 := {i : Usize // i.val < 3}

def Signature557 (α : Type) : Port557 → Type
  | .dependency body => PV_B3Q_PartialCatalogue2.Signature α body
  | .store => Store14
  | .matrix => Matrix14 → MatrixIndex557 → MatrixIndex557 → U64 → Result Matrix14
  | .slice => SliceFn14
  | .fields => Bytes15 → List U32 → Result FieldState13

def source557 (α : Type) : (i : Port557) → Signature557 α i
  | .dependency body => PV_B3Q_PartialCatalogue2.source α body
  | .store => PV_B3Q_D188.direct_store
  | .matrix => fun state row column value =>
      PV_B3Q_Matrix.deployed_store state row.val column.val value
  | .slice => PV_B3Q_FourSlice.source
  | .fields => fun out values => do
      let state ← fields_vec15 out values
      .ok (erase_vec_state15 state)

def model557 (α : Type) : (i : Port557) → Signature557 α i
  | .dependency body => PV_B3Q_PartialCatalogue2.model α body
  | .store => fun _ state index value => Array.update state index value
  | .matrix => fun state row column value =>
      model_matrix_store14 state row.val column.val value
  | .slice => fun step state => PV_B3P_Binding9227.usize_plan step 4 0#usize state
  | .fields => fun out values => fields_model13 append_bytes15 out.val values

/-- The existing closure14 predicate, instantiated jointly with named source
laws. No always-Ok formatter interpretation is used. Missing opaque helpers,
pre-inline/drop/caller associations and native coverage are not inferred. -/
theorem partial_closure557 (α : Type) :
    PV_B3P_Link_std_dependency_closure14 (Signature557 α) (source557 α) (model557 α) := by
  intro i
  cases i with
  | dependency body => exact PV_B3Q_PartialCatalogue2.partial_dependency_link α body
  | store => rfl
  | matrix =>
      funext state row column value
      exact PV_B3Q_Matrix.deployed_store_link state row.val column.val value row.property column.property
  | slice => exact funext fun step => funext (PV_B3Q_FourSlice.source_link step)
  | fields => exact funext fun out => funext (fields_vec_projection15 out)

/-- The original D188 and matrix links are retained verbatim. -/
theorem store_links557 :
    PV_B3P_Link_D188 PV_B3Q_D188.direct_store ∧
    PV_B3P_Link_matrix_stores PV_B3Q_Matrix.deployed_store ∧
    PV_B3P_Link_slice14 PV_B3Q_FourSlice.source :=
  ⟨PV_B3Q_D188.direct_store_link,PV_B3Q_Matrix.deployed_store_link,
    PV_B3Q_FourSlice.source_link⟩

#print axioms partial_closure557
#print axioms store_links557
end PV_B3P_Closure557227
