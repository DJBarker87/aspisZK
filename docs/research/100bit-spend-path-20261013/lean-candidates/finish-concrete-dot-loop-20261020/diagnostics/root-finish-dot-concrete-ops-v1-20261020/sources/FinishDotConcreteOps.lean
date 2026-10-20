import FinishAcceptedRhsCanonical
import EbyKNewToPushStateABI
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotConcreteOps
open AspisR1CurrentWide.Proof AspisR1FinishDotSourceABI AspisR1FinishRelationCurrent
open AspisR1EbyKPushDotBackend

def sourceNewDot : Result PushState := do
  let state ← AspisR1Stage2Accumulate.new_entry
  .ok (EbyKNewToPushStateABI.stateToPush state)

theorem sourceNewDot_zero : sourceNewDot=.ok EbyKNewToPushStateABI.pushZero := by
  obtain ⟨state,hnew,hmap⟩ := EbyKNewToPushStateABI.constructor_new_push_state_compatible
  simp only [sourceNewDot,hnew,bind_tc_ok,hmap]

def toPushQM (q : FinishQM) : PushQm := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toPushWide (v : FinishE) : PushWide := ⟨toPushQM v.c0,toPushQM v.c1⟩

def withConcreteDot {W : Type} (base : FinishOps W PushState) (rawFn : RawFn) : FinishOps W PushState :=
  {base with
    newDot:=sourceNewDot
    pushDot:=fun s v q => pushWithDotBackend rawFn s (toPushWide v) (toPushQM q)
    finishDot:=finishFromPush
    eq:=finishEq}

theorem concrete_dot_push_count {W : Type} (base : FinishOps W PushState) (rawFn : RawFn)
    (s out : PushState) (v : FinishE) (q : FinishQM)
    (hrun : (withConcreteDot base rawFn).pushDot s v q = .ok (.Ok (),out)) :
    out.count.val=s.count.val+1 := by
  obtain ⟨lo,hi,hlo,hhi,hl,hh,hbound,hcount,hcanonical⟩ :=
    successful_push_exact_backend rawFn s (toPushWide v) (toPushQM q) out hrun
  exact hcount

theorem concrete_dot_finish_rhs_canonical {W : Type} (base : FinishOps W PushState) (rawFn : RawFn)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) (hv : p.variant=transport.Variant.S2)
    (hrun : verifier.finish_relation (withConcreteDot base rawFn) v p a obs=.ok (.Ok ())) :
    CanonicalFinish a.rhs := by
  exact AspisR1FinishAcceptedRhsCanonical.successful_S2_finish_rhs_canonical
    (withConcreteDot base rawFn) v p a obs hv hrun

#print axioms sourceNewDot_zero
#print axioms concrete_dot_push_count
#print axioms concrete_dot_finish_rhs_canonical
end AspisR1FinishDotConcreteOps
