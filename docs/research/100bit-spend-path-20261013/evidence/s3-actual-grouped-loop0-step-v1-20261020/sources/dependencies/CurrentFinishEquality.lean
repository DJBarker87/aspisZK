import CurrentFinishArithmetic
import CurrentWideEqSemanticV7
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

def finishEq (x y : FinishE) : Result Bool :=
  field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq (ofFinishE x) (ofFinishE y)

theorem finish_eq_success_true (x y : FinishE) (h : finishEq x y = .ok true) : x=y := by
  have he := wide_partialEq_success_true (ofFinishE x) (ofFinishE y) h
  have hr := congrArg toFinishE he
  simpa only [to_of_finish] using hr

def finishCheckedArithmetic {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) :
    AspisR1FinishRelationCurrent.FinishOps W D :=
  {finishArithmetic ops with eq:=finishEq}

theorem current_checked_round_equation {W D : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (poly : Slice U8) (alpha claim out : FinishE) (round : Usize)
    (hc : CanonicalFinish claim)
    (h0 : ∀ x, ops.field poly 0#usize = .ok x → CanonicalFinish x)
    (h4 : ∀ x, ops.field poly 4#usize = .ok x → CanonicalFinish x)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation_round
      (finishCheckedArithmetic ops) poly alpha claim round = .ok (.Ok out)) :
    ∃ x0 x4, ops.field poly 0#usize=.ok x0 ∧ ops.field poly 4#usize=.ok x4 ∧
      decodeFinish x0+decodeFinish x4=decodeFinish claim * (536870912 : AspisWideTower.WideExact) := by
  have hr := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
    (finishCheckedArithmetic ops) finish_eq_success_true poly alpha claim out round h
  exact current_round_equation ops poly alpha claim out hc h0 h4 hr

#print axioms finish_eq_success_true
#print axioms current_checked_round_equation
end AspisR1CurrentWide.Proof
