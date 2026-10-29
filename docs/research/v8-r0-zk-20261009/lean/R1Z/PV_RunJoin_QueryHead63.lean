import R1Z.PV_RunJoin_QueryCell63
import R1Z.PV_RunJoin_QueryIndexInstalled56
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryHead63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_ResultPost41
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem get (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op76 (types base) (selected base heap box ops)=ProverRwDictionaryDomain.fibreGet := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_76]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem bound (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries) (i : Fin 22) :
    Post (fun pair => pair.1.val<262144)
      (@PV_RunJoin_QueryScript63.head (types base) (selected base heap box ops)
        cc1 cc2 queries (PV_RunJoin_QueryCell63.index i)) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have hi : i.val<queries.val.length := by rw [queries.property];exact i.isLt
  let q := queries.val[i.val]'hi
  have hq : q.val<262144 := range q (List.getElem_mem hi)
  have castBound : (UScalar.cast .Usize q).val<262144 := by
    rw [PV_B2_D_SmallScalar.cast_val]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hq
  have read : Array.index_usize queries (PV_RunJoin_QueryCell63.index i)=ok q := by
    rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by change i.val<22;exact i.isLt)]
    rfl
  have new : aspis_core.r0.domain.FibreIndex.new (UScalar.cast .Usize q)=ok (.Ok (UScalar.cast .Usize q)) := by
    change @ExternalFuns.op75 (types base) (selected base heap box ops) _=_
    rw [PV_RunJoin_QueryIndexInstalled56.installed]
    simp only [ProverRwDictionaryDomain.fibreNew,show UScalar.cast .Usize q<262144#usize from castBound,if_true]
  simp only [PV_RunJoin_QueryScript63.head,read,bind_tc_ok,new,unwrapSlice]
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  apply PV_RunJoin_ResultPost41.bind
  intro first
  apply PV_RunJoin_ResultPost41.bind
  intro second
  exact castBound

#print axioms get
#print axioms bound
end R1Z.PV_RunJoin_QueryHead63
