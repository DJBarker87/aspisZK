import CuSavingsCanonicalDotsCounters
import CuSavingsCanonicalDotsChecked
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsPush
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsCounters CuSavingsCanonicalDotsField CuSavingsCanonicalDotsChecked
variable [Shared]

def projectDot (old : old_pairing.canonical.Dot) : new_pairing.canonical.Dot := ⟨old.sums⟩
def project (old : old_pairing.EbyKDot) : new_pairing.EbyKDot :=
  ⟨projectDot old.c0,projectDot old.c1,old.count⟩
def projectResult (entry : core.result.Result Unit Unit × old_pairing.EbyKDot) :
    core.result.Result Unit Unit × new_pairing.EbyKDot := (entry.1,project entry.2)
def RelatedCounts (old : old_pairing.EbyKDot) : Prop :=
  old.c0.count=old.count ∧ old.c1.count=old.count

theorem dot_push (self : old_pairing.canonical.Dot) (a b : CuSavingsCanonicalDotsChecked.Q) (hc : self.count.val<4096) :
    new_pairing.canonical.Dot.push (projectDot self) a b =
      (do let out ← old_pairing.canonical.Dot.push self a b
          .ok (projectDot out)) := by
  have eta : ∀ r : Result new_pairing.canonical.Dot,
      (do let sums ← loopResult r;.ok (projected sums))=r := by
    intro r
    cases r with
    | fail e => rfl
    | div => rfl
    | ok value => cases value;rfl
  rw [← eta (new_pairing.canonical.Dot.push (projectDot self) a b)]
  have hp : loopResult (new_pairing.canonical.Dot.push (projectDot self) a b)=
      (old_pairing.canonical.Dot.push self a b >>=fun out => .ok out.sums) :=
    push_transport self a b hc
  rw [hp]
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

theorem scalar_checks (value : field.QM31) :
    new_pairing.checked_q value=old_pairing.checked_q value := by
  have hi :
      new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool =
        old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool := by
    unfold new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
      old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
      new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool
      old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool
      new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once
      old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once
      new_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
      old_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
      new_pairing.canonical.P old_pairing.canonical.P
    rfl
  simp only [new_pairing.checked_q,old_pairing.checked_q,new_pairing.limbs_of,
    old_pairing.limbs_of,new_pairing.canonical.Q.from_limbs,old_pairing.canonical.Q.from_limbs,hi]


theorem from_wide (value : field.wide_exact.WideExact) :
    new_pairing.canonical.Q.from_wide value =
      .ok (Array.make 2#usize [limbs value.c0,limbs value.c1]) := by
  simp [new_pairing.canonical.Q.from_wide,field.wide_exact.WideExact.to_limbs,
    Array.index_usize,Array.make,limbs]

theorem public_push (self : old_pairing.EbyKDot) (value : field.wide_exact.WideExact)
    (scalar : field.QM31) (hc : WideCanonical value) (hcounts : RelatedCounts self) :
    new_pairing.EbyKDot.push (project self) value scalar =
      (old_pairing.EbyKDot.push self value scalar >>= fun entry=>.ok (projectResult entry)) := by
  have hmax : new_pairing.MAX_TERMS=old_pairing.MAX_TERMS := by
    simp only [new_pairing.MAX_TERMS,old_pairing.MAX_TERMS]
  by_cases hlimit : self.count>=old_pairing.MAX_TERMS
  · simp only [new_pairing.EbyKDot.push,old_pairing.EbyKDot.push,project,hmax,
      hlimit,↓reduceIte,bind_tc_ok,projectResult]
  · have hbound : self.count.val<4096 := by
      simp only [old_pairing.MAX_TERMS] at hlimit
      scalar_tac
    have hc0 : self.c0.count.val<4096 := by rw [hcounts.1];exact hbound
    have hc1 : self.c1.count.val<4096 := by rw [hcounts.2];exact hbound
    have hnew : new_pairing.EbyKDot.push (project self) value scalar = (do
        let checked ← old_pairing.checked_q scalar
        let cf ← core.result.Result.Insts.CoreOpsTry.branch checked
        match cf with
        | core.ops.control_flow.ControlFlow.Continue scalar => do
          let left ← new_pairing.canonical.Dot.push (projectDot self.c0) (limbs value.c0) scalar
          let right ← new_pairing.canonical.Dot.push (projectDot self.c1) (limbs value.c1) scalar
          let count ← self.count+1#usize
          .ok (.Ok (),⟨left,right,count⟩)
        | core.ops.control_flow.ControlFlow.Break residual => do
          let error ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame Unit) residual
          .ok (error,project self)) := by
      simp only [new_pairing.EbyKDot.push,project,hmax,hlimit,↓reduceIte,
        from_wide,bind_tc_ok,scalar_checks]
      simp [Array.index_usize,Array.make]
      intro result _ flow _
      cases flow <;> rfl
    rw [hnew]
    simp only [old_pairing.EbyKDot.push,hlimit,↓reduceIte,
      field.wide_exact.WideExact.impl.c0,field.wide_exact.WideExact.impl.c1,
      checked_q value.c0 hc.1,checked_q value.c1 hc.2,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    cases hs : old_pairing.checked_q scalar with
    | fail error => rfl
    | div => rfl
    | ok check =>
      cases check with
      | Err error => rfl
      | Ok word =>
        simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
        rw [dot_push self.c0 _ _ hc0,dot_push self.c1 _ _ hc1]
        simp only [bind_assoc_eq,bind_tc_ok,project,projectResult]

#print axioms dot_push
#print axioms scalar_checks
#print axioms from_wide
#print axioms public_push
end AspisR1.CuSavingsCanonicalDotsPush
