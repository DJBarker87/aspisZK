import NDO_JFn_Basis
import NDO_JFn_Rows
import JFn_QueryArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Accumulate
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Forward accumulation from the real decoded checkpoint and actual pending
constructor. The queried node/value are still supplied: this theorem does
not establish geometry, the folding gate or a complete accepted query. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (node : U32) (value : SAQ_WideABI.E)
    (canonical : Port4C_QueryArithmetic.CanonE value) :
    ∃ out after,
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
        JFo_Prepared.value JFo_Prepared.accumulator node value JFo_Pending.value=ok (out,after) ∧
      out.weights=JFo_Prepared.accumulator.weights ∧ out.next=11#usize ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      after.raw.val.length=64 := by
  obtain ⟨basis,hbasis,cbasis,_⟩ := JFn_Basis.source seed node
  obtain ⟨rows,sumOut,hrows,_,progress⟩ := JFn_Rows.source seed basis cbasis
  obtain ⟨product,hproduct,cproduct⟩ := JFn_QueryArithmeticTotal.mulE value
    JFo_Prepared.accumulator.power canonical JFn_AccumulatorCanonical.power
  obtain ⟨rhs,hrhs,crhs⟩ := JFn_QueryArithmeticTotal.add JFo_Prepared.accumulator.rhs product
    JFn_AccumulatorCanonical.rhs cproduct
  obtain ⟨power,hpower,cpower⟩ := JFn_QueryArithmeticTotal.mulK JFo_Prepared.accumulator.power
    JFo_Prepared.value.rho JFn_AccumulatorCanonical.power JFn_AccumulatorCanonical.rho
  have hp : (JFn_ArrayBuilder.ops seed).op3 value JFo_Prepared.accumulator.power=ok product := hproduct
  have hr : (JFn_ArrayBuilder.ops seed).op2 JFo_Prepared.accumulator.rhs product=ok rhs := hrhs
  have hq : (JFn_ArrayBuilder.ops seed).op9 JFo_Prepared.accumulator.power JFo_Prepared.value.rho=ok power := hpower
  have mark : (JFn_ArrayBuilder.ops seed).op15 11#u16 JFo_Prepared.accumulator.next rhs=ok () := rfl
  have next : Usize.wrapping_add JFo_Prepared.accumulator.next 1#usize=11#usize := by
    apply UScalar.eq_of_val_eq
    rw [Port3_Wrapping.increment _ (by change 10<256;decide)]
    rfl
  refine ⟨{JFo_Prepared.accumulator with rhs,power,next:=11#usize},
    {Port3_RowsInstall.fromBW rows with terms:=Usize.wrapping_add (Port3_RowsInstall.fromBW rows).terms 1#usize},
    ?_,rfl,rfl,crhs,cpower,progress.2.1⟩
  rw [Port4C_BasisMeaning.factor _ _ _ _ _ _ JFo_Prepared.weights_length]
  simp only [hbasis,hrows,hp,hr,hq,mark,next,lift,bind_tc_ok]

#print axioms source
end AspisR1.JFn_Accumulate
end
