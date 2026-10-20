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

#print axioms dot_push
#print axioms scalar_checks
end AspisR1.CuSavingsCanonicalDotsPush
