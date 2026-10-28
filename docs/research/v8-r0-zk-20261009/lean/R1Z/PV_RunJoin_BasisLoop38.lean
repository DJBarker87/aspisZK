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
    have kd : (Usize.wrapping_sub k 1#usize).val=n := by scalar_tac
    have ld : (U8.wrapping_sub left 1#u8).val=n := by scalar_tac
    have same : UScalar.cast .Usize (U8.wrapping_sub left 1#u8)=
        Usize.wrapping_sub k 1#usize := by scalar_tac
    unfold host_sumcheck.interpolation_extend_loop
    rw [ProverRw19LoopBind.loop_bind,AspisR1ProducerRelease47.basis_mul]
    simp only [host_sumcheck.interpolation_extend_loop.body,kp,↓reduceIte,ln,lift,bind_tc_ok,same]
    rw [PV_RunJoin_BasisCell38.update]
    change (do
      let next ← cell basis (Usize.wrapping_sub k 1#usize) (UScalar.cast .U32 j)
      @host_sumcheck.interpolation_extend_loop _ (ProverRwP6BodyCandidate.selected ops)
        next j (Usize.wrapping_sub k 1#usize)) =
      (do
      let next ← cell basis (Usize.wrapping_sub k 1#usize) (UScalar.cast .U32 j)
      AspisR1ProducerRelease47.basis_mul next (UScalar.cast .U32 j) (U8.wrapping_sub left 1#u8))
    apply congrArg (Aeneas.Std.bind (cell basis (Usize.wrapping_sub k 1#usize) (UScalar.cast .U32 j)))
    funext next
    exact ih _ _ kd ld (by omega) next

#print axioms source
end R1Z.PV_RunJoin_BasisLoop38
