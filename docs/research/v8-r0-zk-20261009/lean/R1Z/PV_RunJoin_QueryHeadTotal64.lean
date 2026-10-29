import R1Z.PV_RunJoin_QueryFillTotal64
import R1Z.PV_RunJoin_InactiveFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryHeadTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (domain1 : PV_RunJoin_QueryFillStep64.Domain cc1)
    (domain2 : PV_RunJoin_QueryFillStep64.Domain cc2)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (i : Fin 22) :
    ∃ pair, @PV_RunJoin_QueryScript63.head (types base) (selected base heap box ops)
      cc1 cc2 queries (PV_RunJoin_QueryCell63.index i)=ok pair ∧ pair.1.val<262144 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have hi : i.val<queries.val.length := by rw [queries.property];exact i.isLt
  let q := queries.val[i.val]'hi
  let u := UScalar.cast .Usize q
  have bound : u.val<262144 := by
    dsimp only [u]
    rw [PV_B2_D_SmallScalar.cast_val]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (range q (List.getElem_mem hi))
  have read : Array.index_usize queries (PV_RunJoin_QueryCell63.index i)=ok q :=
    ProverCommitArrayIndex25.array_index_usize_ok queries (PV_RunJoin_QueryCell63.index i) (by change i.val<22;exact i.isLt)
  have new : aspis_core.r0.domain.FibreIndex.new u=ok (.Ok u) := by
    change (selected base heap box ops).op75 u=_
    rw [PV_RunJoin_QueryIndexInstalled56.installed]
    simp only [ProverRwDictionaryDomain.fibreNew,show u<262144#usize from bound,if_true]
  obtain ⟨zero,hzero⟩ : ∃ zero, aspis_core.field.wide_exact.WideExact.ZERO=ok zero :=
    ⟨_,PV_RunJoin_InactiveFields48.zero base heap box ops⟩
  let opening : aspis_core.r0.wire.FibreOpening :=
    ⟨Array.repeat 4#usize (Array.repeat 29#usize zero),
      Array.repeat 2#usize (Array.repeat 6#usize (Array.repeat 7#usize (Array.repeat 32#usize 0#u8)))⟩
  obtain ⟨first,hfirst⟩ := PV_RunJoin_QueryFillTotal64.complete base heap box ops cc1 domain1 u bound opening
  obtain ⟨second,hsecond⟩ := PV_RunJoin_QueryFillTotal64.complete base heap box ops cc2 domain2 u bound first
  dsimp only [u,opening] at new hfirst hsecond
  refine ⟨(u,second),?_,bound⟩
  simp only [PV_RunJoin_QueryScript63.head,read,bind_tc_ok,new,unwrapSlice,hzero,hfirst,hsecond,u]

#print axioms complete
end R1Z.PV_RunJoin_QueryHeadTotal64
