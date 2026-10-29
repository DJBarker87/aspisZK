import R1Z.PV_RunJoin_QueryEncoded63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryAccess64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
variable [ExternalTypes] [ExternalFuns]

theorem vector {T : Type} (v : alloc.vec.Vec T) (i : Usize) (bound : i.val<v.length) :
    ∃ x, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) v i=ok x := by
  have h : i.val<v.val.length := bound
  refine ⟨v.val[i.val]'h,?_⟩
  simp only [alloc.vec.Vec.index,core.slice.index.Slice.index,
    core.slice.index.SliceIndexUsizeSlice,core.slice.index.SliceIndexUsizeSlice.index,
    alloc.vec.Vec.deref]
  simp only [Slice.index_usize,List.getElem?_eq_getElem h]

theorem salt (v : host_commitment.PrivateSalts) (i : Usize) (bound : i.val<v.length) :
    ∃ x, host_commitment.PrivateSalts.get v i=ok x := vector v i bound

/-- The query's four-cell window is in range when the contextual folded word
has the source domain length. This is totality, rather than a postcondition
that is trivially true on errors. -/
theorem window (folded : Slice aspis_core.field.wide_exact.WideExact)
    (size : 262144≤folded.length) (q : Usize) (bound : q.val<262144) :
    ∃ values, PV_RunJoin_QueryWindow63.window folded q=ok values ∧ values.length=4 := by
  obtain ⟨quarter,hquarter,hval⟩ := UScalar.div_spec q (y:=4#usize) (by decide)
  have hq : quarter.val<65536 := by omega
  have hm := PV_RunJoin_QueryWindow63.mul4 quarter hq
  have ha := PV_RunJoin_QueryWindow63.add4 (Usize.wrapping_mul 4#usize quarter) (by rw [hm];omega)
  let first := Usize.wrapping_mul 4#usize quarter
  let last := Usize.wrapping_add first 4#usize
  have guards : first.val≤last.val ∧ last.val≤folded.length := by
    dsimp only [first,last]
    rw [ha,hm]
    omega
  have total : ∃ values, PV_RunJoin_QueryWindow63.window folded q=ok values := by
    simp only [PV_RunJoin_QueryWindow63.window,hquarter,bind_tc_ok]
    simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
      core.slice.index.SliceIndexRangeUsizeSlice.index]
    simp only [guards.1,guards.2,and_self,if_true]
    exact ⟨_,rfl⟩
  obtain ⟨values,success⟩ := total
  exact ⟨values,success,PV_RunJoin_ResultPost41.success _ _ _
    (PV_RunJoin_QueryWindow63.length folded q bound) success⟩

#print axioms vector
#print axioms salt
#print axioms window
end R1Z.PV_RunJoin_QueryAccess64
