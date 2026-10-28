import R1Z.PV_RunJoin_Foundation34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoundationValues34
open Aeneas Aeneas.Std Result PV_RunJoin_HonestIdentification26
open ProverRw21CallerFoundation
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def values (i : Honest (K := K)) : Fin 16 → Fin 1024 → M := fun lane row =>
  (column (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) lane)[row.val]'
    (by rw [PV_RunJoin_Foundation34.shape i lane]; exact row.isLt)

theorem decode_values (i : Honest (K := K)) :
    decode (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) = some (values i) :=
  success _ (PV_RunJoin_Foundation34.shape i)

theorem value_word (i : Honest (K := K)) (lane : Fin 16) (row : Fin 1024) :
    values i lane row =
      ((PV_Src_Forest_Columns.read i.val.compiled.semantic_c1.c1
        ⟨lane.val,by have := lane.isLt; omega⟩ row).val : M) := by
  have hc : lane.val < i.val.compiled.semantic_c1.c1.val.length := by
    rw [i.val.compiled.semantic_c1.c1.property]; exact lane.isLt
  have hr : (rawColumn (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) lane).val.length = 1024 := by
    rw [← column_length]; exact PV_RunJoin_Foundation34.shape i lane
  have hr' : row.val < (i.val.compiled.semantic_c1.c1.val[lane.val]).val.length := by
    change row.val < (rawColumn (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) lane).val.length
    rw [hr]; exact row.isLt
  simp only [values,column,List.getElem_map,rawColumn,PV_RunJoin_NominalLeafData.foundation,
    PV_Src_Forest_Columns.read,if_pos lane.isLt,Fin.val_mk,
    getElem!_pos i.val.compiled.semantic_c1.c1.val lane.val hc,
    getElem!_pos (i.val.compiled.semantic_c1.c1.val[lane.val]).val row.val hr']

theorem canonical_cell (i : Honest (K := K)) (lane : Fin 16) (row : Fin 1024) :
    algebraMap M K (values i lane row) =
      BuilderSource.prover.build (target i) ⟨lane.val,by have := lane.isLt; omega⟩ row := by
  rw [value_word]
  rw [← build_eq i]
  change algebraMap M K ((_ : U32).val : M) = R0Z.WriterRefine.liftU _
  simp only [map_natCast,R0Z.WriterRefine.liftU,inputs]

#print axioms values
#print axioms decode_values
#print axioms value_word
#print axioms canonical_cell
end R1Z.PV_RunJoin_FoundationValues34
