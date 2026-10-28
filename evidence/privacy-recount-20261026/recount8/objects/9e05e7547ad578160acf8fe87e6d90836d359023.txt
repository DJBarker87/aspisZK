import R1Z.ProverCommitInterpolationIndices48
import R1Z.PV_RunJoin_BasisLoop38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisExtend38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BasisCell38
variable [ExternalTypes]

/-- One factor's complete descending update, including its symbolic counter
conversion. The bound excludes wraparound before the counter is cast. -/
theorem source (ops : ExternalFuns) (basis : MA) (degree j : Usize)
    (bound : degree.val+2≤28) :
    @host_sumcheck.interpolation_extend _ (ProverRwP6BodyCandidate.selected ops) basis degree j =
      AspisR1ProducerRelease47.basis_mul basis (UScalar.cast .U32 j)
        (U8.wrapping_add (UScalar.cast .U8 degree) 2#u8) := by
  have hk : (Usize.wrapping_add degree 2#usize).val=degree.val+2 := by
    rw [Usize.wrapping_add_val_eq]
    change (degree.val+2)%UScalar.size .Usize=degree.val+2
    apply Nat.mod_eq_of_lt
    have big := (28#usize).hSize
    change 28<UScalar.size .Usize at big
    omega
  have castval : (UScalar.cast .U8 degree).val=degree.val := by scalar_tac
  have hl : (U8.wrapping_add (UScalar.cast .U8 degree) 2#u8).val=degree.val+2 := by
    rw [U8.wrapping_add_val_eq,castval,ProverCommitInterpolationIndices48.size_u8]
    change (degree.val+2)%256=degree.val+2
    exact Nat.mod_eq_of_lt (by omega)
  unfold host_sumcheck.interpolation_extend
  simp only [lift,bind_tc_ok]
  exact PV_RunJoin_BasisLoop38.source ops (degree.val+2) _ _ hk hl bound basis j

#print axioms source
end R1Z.PV_RunJoin_BasisExtend38
