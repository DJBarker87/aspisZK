import FIr_TerminalTrace
import FIr_EqualityValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_TerminalValue
open Aeneas Aeneas.Std Result
open FIr_NativeValue (Canon decode K)
open FIr_TerminalTrace

def formula (eq comp mu h active : K) : K :=
  eq*comp+mu*h+mu^2*(1-active)*h

/-- Exact arithmetic of the installed native terminal tail. Canonicality of
its three composition outputs remains an explicit local obligation. -/
theorem arithmetic (left right : Array NQ 10#usize) (mu comp h active out : NQ)
    (calls : Calls left right mu comp h active out)
    (hl : ∀ x∈left.val,Canon x) (hr : ∀ x∈right.val,Canon x)
    (hmu : Canon mu) (hc : Canon comp) (hh : Canon h) (ha : Canon active) :
    Canon out ∧ decode out=formula (FIr_EqualityValue.weight left right)
      (decode comp) (decode mu) (decode h) (decode active) := by
  have eq := FIr_EqualityValue.exact_value left right hl hr calls.eq calls.equality
  have w := FIr_NativeValue.mul calls.eq comp calls.weighted eq.1 hc calls.weight
  have mh := FIr_NativeValue.mul mu h calls.muH hmu hh calls.mu_h
  have s := FIr_NativeValue.add calls.weighted calls.muH calls.sum w.1 mh.1 calls.sum_call
  have m2 := FIr_NativeValue.mul mu mu calls.mu2 hmu hmu calls.mu_square
  have inactive := FIr_NativeSub.qm FIq_Native.field.QM31.ONE active calls.inactive
    FIr_NativeValue.one.1 ha calls.inactive_call
  have ih := FIr_NativeValue.mul calls.inactive h calls.inactiveH inactive.1 hh calls.inactive_h
  have extra := FIr_NativeValue.mul calls.mu2 calls.inactiveH calls.extra m2.1 ih.1 calls.extra_call
  have result := FIr_NativeValue.add calls.sum calls.extra out s.1 extra.1 calls.returned
  refine ⟨result.1,?_⟩
  rw [result.2,s.2,extra.2,w.2,mh.2,m2.2,ih.2,inactive.2,FIr_NativeValue.one.2,eq.2]
  unfold formula
  ring

#print axioms arithmetic
end AspisR1.FIr_TerminalValue
end
