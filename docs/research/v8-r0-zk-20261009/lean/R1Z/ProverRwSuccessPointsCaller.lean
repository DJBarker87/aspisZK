import R1Z.ProverRwSuccessPointsTotal
import R1Z.ProverRwSuccessBodyInterpretation
set_option autoImplicit false
namespace R1Z.ProverRwSuccessPointsCaller
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwSuccessPointsFinite ProverRwSuccessReverseRange ProverRwSuccessArithmeticTotal

theorem source_total (z : Points) :
    Total (ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points z) := by
  have len : Slice.len (Array.to_slice z)=10#usize := by
    apply UScalar.eq_of_val_eq
    change z.val.length=10
    exact z.property
  unfold ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points
  simp only [lift,bind_tc_ok,len,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  apply bind_total (ProverRwSuccessPointsTotal.loop_total z z _);intro successor
  apply bind_total ⟨_,ProverCommitArrayIndex25.array_index_usize_ok z 7#usize (by decide)⟩;intro q
  apply bind_total (ProverRwSuccessQuarticTotal.sub _ _);intro q1
  apply bind_total (ProverRwSuccessPointsTotal.update_total _ _ _ (by decide));intro absorption
  apply bind_total ⟨_,ProverCommitArrayIndex25.array_index_usize_ok absorption 6#usize (by decide)⟩;intro q2
  apply bind_total (ProverRwSuccessQuarticTotal.sub _ _);intro q3
  apply bind_total (ProverRwSuccessPointsTotal.update_total _ _ _ (by decide));intro final
  exact ok_total _

variable [ExternalTypes]
theorem installed_total (ops : ExternalFuns) (z : Points) :
    Total ((ProverRwSuccessBodyInterpretation.selected ops).op118 z) := source_total z
#print axioms source_total
#print axioms installed_total
end R1Z.ProverRwSuccessPointsCaller
