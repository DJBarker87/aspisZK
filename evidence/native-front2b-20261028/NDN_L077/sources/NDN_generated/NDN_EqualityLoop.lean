import NDE_RowBridge
import RPv_FIx_ArithmeticTotal
import RPu_FIq_Native14
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDN_EqualityLoop
open AspisR1
abbrev Q := FIq_Native.field.QM31
open FIv_NativeValue (Canon)
abbrev factor := FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
abbrev loop := FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop

def FactorDomain (left right : Array Q 10#usize) : Prop :=
 ∀ i : Usize,i.val<10 → ∃ a b out,
  Array.index_usize left i=ok a ∧ Array.index_usize right i=ok b ∧
  factor () (a,b)=ok out ∧ Canon out

theorem total (fuel : Nat) (left right : Array Q 10#usize) (product : Q) (i : Usize)
 (hi:i.val+fuel=10) (hp:Canon product) (hf:FactorDomain left right) :
 ∃ out,loop left right product i=ok out ∧ Canon out := by
 induction fuel generalizing i product with
 | zero =>
  have bound : ¬ i<10#usize := by scalar_tac
  refine ⟨product,?_,hp⟩
  rw [FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop.eq_def]
  simp only [Array.to_slice,Slice.len,lift,bind_tc_ok,left.property,if_neg bound]
 | succ fuel ih =>
  have bound : i.val<10 := by omega
  obtain ⟨a,b,f,ha,hb,hf',hcf⟩:=hf i bound
  obtain ⟨next,hn,hcn,_⟩:=FIx_ArithmeticTotal.mul product f hp hcf
  obtain ⟨j,hj,hjv⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  obtain ⟨out,ho,hco⟩:=ih (i:=j) (product:=next) (by scalar_tac) hcn
  refine ⟨out,?_,hco⟩
  rw [FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop.eq_def]
  have guard : i<10#usize := by scalar_tac
  simp only [Array.to_slice,Slice.len,lift,bind_tc_ok,left.property,if_pos guard,
    ha,hb,hf',hn,hj]
  exact ho

theorem source_total (left right : Array Q 10#usize) (hf:FactorDomain left right) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value left right=ok out ∧ Canon out := by
 obtain ⟨a,b,f,ha,hb,hf',hcf⟩:=hf 0#usize (by decide)
 obtain ⟨out,ho,hco⟩:=total 9 left right f 1#usize rfl hcf hf
 refine ⟨out,?_,hco⟩
 unfold FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value
 rw [ha,bind_tc_ok,hb,bind_tc_ok,hf',bind_tc_ok]
 exact ho

#print axioms total
#print axioms source_total
end NDN_EqualityLoop
end
