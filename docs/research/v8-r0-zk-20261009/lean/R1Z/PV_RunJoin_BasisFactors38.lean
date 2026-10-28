import R1Z.PV_RunJoin_BasisEquation38
import R1Z.PV_RunJoin_BasisExtend38
import R1Z.PV_RunJoin_InterpolationCounters38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisFactors38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BasisCell38 ProverCommitInterpolationSchedule48
variable [ExternalTypes]

/-- Complete source basis-factor recurrence, including the omitted node and
all descending writes. The degree invariant discharges every counter bound. -/
theorem source (ops : ExternalFuns) (n : Nat) (i j d : Usize) (left : U8)
    (hi : i.val<28) (hcount : j.val+n=28) (hl : left.val=n)
    (hd : d.val=degree i.val j.val) (basis : MA) (den : U32) :
    @host_sumcheck.interpolation_basis_steps _ (ProverRwP6BodyCandidate.selected ops)
      basis den d i j =
    AspisR1ProducerRelease47.basis_factors basis den (UScalar.cast .U8 d)
      (UScalar.cast .U8 i) (UScalar.cast .U8 j) left := by
  induction n generalizing j d left basis den with
  | zero =>
    have jz : j=28#usize := by scalar_tac
    have lz : left=0#u8 := by scalar_tac
    subst j
    subst left
    rw [@PV_RunJoin_BasisEquation38.step _ (ProverRwP6BodyCandidate.selected ops) basis den d i 28#usize,
      AspisR1ProducerRelease47.basis_factors]
    simp only [↓reduceIte]
  | succ n ih =>
    have hj : j.val<28 := by omega
    have jn : j≠28#usize := by scalar_tac
    have ln : left≠0#u8 := by scalar_tac
    have incj := PV_RunJoin_MergeLoop35.increment j (by omega)
    have decl : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)]
      omega
    rw [@PV_RunJoin_BasisEquation38.step _ (ProverRwP6BodyCandidate.selected ops) basis den d i j,
      AspisR1ProducerRelease47.basis_factors]
    simp only [jn,ln,↓reduceIte]
    by_cases he : i=j
    · have hcast : UScalar.cast .U8 i=UScalar.cast .U8 j := congrArg _ he
      simp only [if_pos he,if_pos hcast,lift,bind_tc_ok]
      have nextDegree : d.val=degree j.val (Usize.wrapping_add j 1#usize).val := by
        rw [incj,skipped_degree]
        simpa only [he] using hd
      rw [ih (Usize.wrapping_add j 1#usize) d (U8.wrapping_sub left 1#u8)
        (by rw [incj];omega) decl (by simpa only [he] using nextDegree) basis den]
      rw [PV_RunJoin_InterpolationCounters38.increment j hj]
    · have hne : i.val≠j.val := by intro eq;apply he;exact UScalar.eq_of_val_eq eq
      have hcast : UScalar.cast .U8 i≠UScalar.cast .U8 j := by scalar_tac
      have room : d.val+2≤28 := PV_RunJoin_InterpolationCounters38.extend_room
        _ _ _ hi hj hd hne
      have incd := PV_RunJoin_MergeLoop35.increment d (by omega)
      have nextDegree : (Usize.wrapping_add d 1#usize).val=
          degree i.val (Usize.wrapping_add j 1#usize).val := by
        rw [incd,incj,selected_degree _ _ hne,hd]
      have tail : ∀ basis1 den1,
          @host_sumcheck.interpolation_basis_steps _ (ProverRwP6BodyCandidate.selected ops)
            basis1 den1 (Usize.wrapping_add d 1#usize) i (Usize.wrapping_add j 1#usize) =
          AspisR1ProducerRelease47.basis_factors basis1 den1
            (U8.wrapping_add (UScalar.cast .U8 d) 1#u8) (UScalar.cast .U8 i)
            (U8.wrapping_add (UScalar.cast .U8 j) 1#u8) (U8.wrapping_sub left 1#u8) := by
        intro basis1 den1
        rw [ih _ _ _ (by rw [incj];omega) decl nextDegree basis1 den1,
          PV_RunJoin_InterpolationCounters38.increment j hj,
          PV_RunJoin_InterpolationCounters38.increment d (by omega)]
      simp only [he,hcast,↓reduceIte,lift,bind_tc_ok]
      rw [PV_RunJoin_BasisExtend38.source ops basis d j room]
      simp only [PV_RunJoin_InterpolationCounters38.cast32 i (by omega),
        PV_RunJoin_InterpolationCounters38.cast32 j (by omega),tail]
      rfl

#print axioms source
end R1Z.PV_RunJoin_BasisFactors38
