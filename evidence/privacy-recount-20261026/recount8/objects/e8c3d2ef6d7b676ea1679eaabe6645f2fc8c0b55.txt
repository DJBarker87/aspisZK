import R1Z.PV_RunJoin_BasisCell38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisLoop38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BasisCell38
variable [ExternalTypes]

/-- The actual descending usize loop equals the retained release basis
recurrence, preserving every Result constructor, including index failures.
Only the two small counters and their range are associated. -/
theorem source (ops : ExternalFuns) (n : Nat) (k : Usize) (left : U8)
    (hk : k.val=n) (hl : left.val=n) (bound : n≤28) (basis : MA) (j : Usize) :
    @host_sumcheck.interpolation_extend_loop _ (ProverRwP6BodyCandidate.selected ops) basis j k =
      AspisR1ProducerRelease47.basis_mul basis (UScalar.cast .U32 j) left := by
  induction n generalizing k left basis with
  | zero =>
    have kz : k=0#usize := by scalar_tac
    have lz : left=0#u8 := by scalar_tac
    subst k
    subst left
    unfold host_sumcheck.interpolation_extend_loop
    rw [ProverRw19LoopBind.loop_bind,AspisR1ProducerRelease47.basis_mul]
    simp only [host_sumcheck.interpolation_extend_loop.body,show ¬(0#usize>0#usize) from by decide,
      ↓reduceIte,bind_tc_ok]
  | succ n ih =>
    have kp : k>0#usize := by change 0<k.val;omega
    have ln : left≠0#u8 := by scalar_tac
    have kd : (Usize.wrapping_sub k 1#usize).val=n := by
      rw [ProverCommitSampleBits49.sub_value k 1#usize (by change 1≤k.val;omega)]
      change k.val-1=n
      omega
    have ld : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)]
      omega
    have same : UScalar.cast .Usize (U8.wrapping_sub left 1#u8)=
        Usize.wrapping_sub k 1#usize := by scalar_tac
    unfold host_sumcheck.interpolation_extend_loop
    rw [ProverRw19LoopBind.loop_bind,AspisR1ProducerRelease47.basis_mul]
    simp only [host_sumcheck.interpolation_extend_loop.body,kp,↓reduceIte,ln,lift,bind_tc_ok,same]
    rw [PV_RunJoin_BasisCell38.update]
    simp only [cell,bind_assoc_eq,bind_tc_ok]
    apply congrArg (Aeneas.Std.bind (AspisR1ProducerRelease47.predecessor basis (Usize.wrapping_sub k 1#usize)))
    funext shifted
    apply congrArg (Aeneas.Std.bind (Array.index_usize basis (Usize.wrapping_sub k 1#usize)))
    funext m
    apply congrArg (Aeneas.Std.bind (AspisR1ProducerRelease47.field.M31.mul m (UScalar.cast .U32 j)))
    funext product
    apply congrArg (Aeneas.Std.bind (AspisR1ProducerRelease47.field.M31.sub shifted product))
    funext value
    apply congrArg (Aeneas.Std.bind (Array.update basis (Usize.wrapping_sub k 1#usize) value))
    funext next
    exact ih _ _ kd ld (by omega) next

#print axioms source
end R1Z.PV_RunJoin_BasisLoop38
