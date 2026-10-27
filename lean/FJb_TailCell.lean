import FJb_MaskColumn
import FJb_ColumnTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_TailCell
open Aeneas Aeneas.Std Result FIq_Native
open FJb_ColumnTable (Table)
def cell {T : Type} {N : Usize} (a : Array T N) (i : Fin N.val) : T :=
  a.val[i.val]'(by simpa only [a.property] using i.isLt)
def Bounded (sums : Table) : Prop :=
  ∀ c i : Fin (4#usize).val,(cell (cell sums c) i).val < 2^34
abbrev call := state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut

theorem value (a : Array U32 4#usize) (sums : Table) (index limb : Usize)
    (hi : limb.val < (4#usize).val) (hs : Bounded sums) :
    ∃ out,call (a,sums,index) limb=ok (out,(a,sums,index)) ∧
      out.val=(cell a ⟨limb.val,hi⟩).val+
        (cell (cell sums ⟨(index &&& 3#usize).val,FJb_MaskColumn.bound index⟩) ⟨limb.val,hi⟩).val ∧
      out.val < 2^35 := by
  let x := cell a ⟨limb.val,hi⟩
  let row := cell sums ⟨(index &&& 3#usize).val,FJb_MaskColumn.bound index⟩
  let y := cell row ⟨limb.val,hi⟩
  have rx : Array.index_usize a limb=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a limb hi
  have rr : Array.index_usize sums (index &&& 3#usize)=ok row :=
    RawPoseidonExternalRowReads.array_index_usize_ok sums _ (FJb_MaskColumn.bound index)
  have ry : Array.index_usize row limb=ok y := RawPoseidonExternalRowReads.array_index_usize_ok row limb hi
  have hx : x.val < 2^32 := x.bv.isLt
  have hy : y.val < 2^34 := hs _ _
  have hadd : (FJb_WideSum4.wide x+y : Result U64) ⦃z=>z.val=(FJb_WideSum4.wide x).val+y.val⦄ := by
    apply UScalar.add_spec
    rw [FJb_WideSum4.wide_val]
    scalar_tac
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists hadd
  refine ⟨out,?_,?_,?_⟩
  · change (do
      let x ← Array.index_usize a limb
      let w ← lift (core.convert.num.FromU64U32.from x)
      let c ← lift (index &&& 3#usize)
      let r ← Array.index_usize sums c
      let y ← Array.index_usize r limb
      let z ← w+y
      ok (z,(a,sums,index)))=ok (out,(a,sums,index))
    simp only [rx,rr,ry,lift,bind_tc_ok]
    change (do let z ← FJb_WideSum4.wide x+y;ok (z,(a,sums,index)))=ok (out,(a,sums,index))
    rw [hr,bind_tc_ok]
  · simpa only [FJb_WideSum4.wide_val] using hv
  · rw [FJb_WideSum4.wide_val] at hv
    omega
#print axioms value
end AspisR1.FJb_TailCell
end
